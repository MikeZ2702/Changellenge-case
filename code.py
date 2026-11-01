from collections import deque
from dataclasses import dataclass
from datetime import datetime, timedelta
from statistics import median

data_of_susp_acc: set[int] = set()
data_of_susp_devices: set[int] = set()
data_of_acc: dict[int, dict[int, "Account"]] = {}
data_of_operations: set[int] = set()
last_fin_events: dict[int, datetime] = {}
risk_threshold: int = 60
susp_threshold: int = 60
MAX_INDEX: int = 100
ANX_HALF_LIFE: timedelta = timedelta(hours=48)
SUSP_HALF_LIFE: timedelta = timedelta(days=7)


TRANSFER_WEIGHTS = (
    100,  # получатель есть в подтверждённом списке мошеннических клиентов
    100,  # устройство есть в подтверждённом списке
    30,   # внешний сигнал о подозрительной активности за 6 часов
    15,   # изменение данных за 48 часов
    45,   # предупреждение платёжной инфраструктуры по этой операции
    45,   # полный триггер: крупный собственный СБП и новый физлицо-получатель
    30,   # индекс подозрительности получателя достиг порога
)

WITHDRAWAL_WEIGHTS = (
    30,   # внешний сигнал за 6 часов
    15,   # изменение данных за 48 часов
    45,   # предупреждение инфраструктуры по этой операции
    40,   # недавнее подходящее финансовое событие или собственный СБП
    30,   # пять и более предыдущих отказов в снятии за день
    50,   # превышена техническая норма APDU для банкомата
    100,  # подтверждённое мошенническое устройство
)

TOP_UP_WEIGHTS = (
    45,   # предупреждение инфраструктуры по этой операции
    50,   # превышена техническая норма APDU
    100,  # подтверждённое мошенническое устройство
)

CARD_WEIGHTS = (
    100,  # подтверждённое мошенническое устройство
    45,   # предупреждение инфраструктуры по этой покупке
)


def _decay_index(value: int, elapsed: timedelta, half_life: timedelta) -> int:
    if half_life <= timedelta(0):
        raise ValueError("период полураспада должен быть положительным")
    if elapsed <= timedelta(0):
        return value

    factor = 0.5 ** (elapsed.total_seconds() / half_life.total_seconds())
    return min(MAX_INDEX, max(0, round(value * factor)))


def decay_anx_index(value: int, elapsed: timedelta) -> int:
    return _decay_index(value, elapsed, ANX_HALF_LIFE)


def decay_susp_index(value: int, elapsed: timedelta) -> int:
    return _decay_index(value, elapsed, SUSP_HALF_LIFE)


def score_flags(flags: list[bool], weights: tuple[int, ...]) -> int:
    if len(flags) != len(weights):
        raise ValueError("число флагов не совпадает с числом весов")

    return min(
        MAX_INDEX,
        sum(weight for flag, weight in zip(flags, weights) if flag),
    )


def add_index_points(current: int, points: int) -> int:
    """Не позволяет индексу выйти за диапазон 0–100."""
    return min(MAX_INDEX, max(0, current + points))


def client_had_recent_relation(
    client_id: int,
    person_id: int,
    now: datetime,
) -> bool:
    return any(
        account.had_recent_relation(person_id, now)
        for account in data_of_acc.get(client_id, {}).values()
    )


def client_self_sbp_sum_24h(client_id: int, now: datetime) -> int:
        total = 0
        window = timedelta(hours=24)
        for account in data_of_acc.get(client_id, {}).values():
            account.transf_from_another_bank = deque(
                (amount, event_at)
                for amount, event_at in account.transf_from_another_bank
                if is_within_window(event_at, now, window)
            )
            total += sum(amount for amount, _ in account.transf_from_another_bank)
        return total


class BankException(Exception):
    pass


@dataclass
class OperationContext:
    operation_id: int
    channel: str  # "SBP", "CARD", "ATM"
    occurred_at: datetime
    device_id: int

    # Ответ платёжной инфраструктуры именно по этой операции
    payment_network_risk: bool = False
    payment_network_source: str | None = None

    # Замер обмена данными с картой в банкомате
    apdu_response_ms: int | None = None
    apdu_limit_ms: int | None = None


@dataclass
class OperationRecord:
    kind: str                     # transfer_out, transfer_in, cash_withdrawal, cash_deposit, card_purchase
    amount: int                   # копейки
    context: OperationContext
    counterparty_id: int | None = None
    status: str = "completed"     # completed или blocked


def has_apdu_risk(operation: OperationContext) -> bool:
    return (
        operation.channel == "ATM"
        and operation.apdu_response_ms is not None
        and operation.apdu_limit_ms is not None
        and operation.apdu_response_ms > operation.apdu_limit_ms
    )


def is_within_window(
    event_at: datetime | None,
    now: datetime,
    window: timedelta,
) -> bool:
    return event_at is not None and now - window <= event_at <= now


def ensure_new_operation(context: OperationContext) -> None:
    if context.operation_id in data_of_operations:
        raise ValueError("операция уже обработана")


class Account:
    def __init__(self, id: int, acc_id: int, balance: int, bank_id: int, pin: str, is_abroad: bool, is_indiv: bool):
        self.anx_ind: int = 0   # индекс тревожности
        self.susp_ind: int = 0  # индекс подозрительности
        self.id: int = id   # id пользователя
        self.acc_id: int = acc_id   # id счёта
        self.bank_id = bank_id  # id банка
        self.is_indiv = is_indiv    # клиент физлицо или нет
        self.pin: str = pin # пин-код
        self.balance: int = balance # баланс
        self.operation_history: deque[OperationRecord] = deque()    # история операций за 180 дней
        self.devices: set[int] = set()  # устройства
        self.recipients: dict[int, datetime] = {}   # получатели за последние 180 дней
        self.transfers_to_acc: dict[int, datetime] = {} # отправители за последние 180 дней
        self.sum_per_day: deque[int] = deque([0], maxlen=180)    # траты за последние 180 дней
        self.last_susp_activity: datetime | None = None # дата последней подозрительной активности
        self.last_data_change: datetime | None = None # последние изменения данных
        self.transf_from_another_bank: deque[tuple[int, datetime]] = deque()    # свои переводы из другого банка за последние 24 часа
        self.last_big_cross_boarder_pay: datetime | None = None # последний крупный перевод за границу
        self.count_refuses_to_prov_cash: int = 0    # количество отказов в снятии средств за день
        self.is_abroad: bool = is_abroad    # зарубежный ли счёт
        self.last_index_decay_at: datetime | None = None    # время последнего затухания индексов
        accounts = data_of_acc.setdefault(id, {})
        if acc_id in accounts:
            raise ValueError("такой счёт клиента уже существует")
        accounts[acc_id] = self


    def record_operation(
        self,
        kind: str,
        amount: int,
        context: OperationContext,
        counterparty_id: int | None = None,
        status: str = "completed",
    ) -> None:
        self.operation_history.append(
            OperationRecord(
                kind=kind,
                amount=amount,
                context=context,
                counterparty_id=counterparty_id,
                status=status,
            )
        )


    def _amount_anomaly_points(
        self,
        kind: str,
        amount: int,
        context: OperationContext,
            peer_id: int | None = None,
    ) -> int:
        cutoff = context.occurred_at - timedelta(days=30)
        history = [
            record
            for record in self.operation_history
            if record.kind == kind
            and record.status == "completed"
            and record.amount > 0
            and cutoff <= record.context.occurred_at < context.occurred_at
        ]

        # Если с этим получателем или продавцом было не меньше пяти операций,
        # сравниваем сумму именно с ними. Иначе — со всеми операциями этого типа.
        peer_history = [
            record for record in history
            if peer_id is not None and record.counterparty_id == peer_id
        ]
        baseline_records = peer_history if len(peer_history) >= 5 else history

        if len(baseline_records) < 5:
            return 0

        typical_amount = median(record.amount for record in baseline_records)
        if typical_amount <= 0:
            return 0

        ratio = amount / typical_amount

        if ratio >= 10:
            return 15
        if ratio >= 5:
            return 10
        if ratio >= 3:
            return 5
        return 0


    def had_recent_relation(self, person_id: int, now: datetime) -> bool:
        cutoff = now - timedelta(days=180)
        dates = (
            self.recipients.get(person_id),
            self.transfers_to_acc.get(person_id),
        )
        return any(date is not None and cutoff <= date <= now for date in dates)


    def risk_of_transfer(self, risk_flags: list[bool], amount: int, context: OperationContext) -> int:
        flags_score = score_flags(risk_flags, TRANSFER_WEIGHTS)
        amount_score = self._amount_anomaly_points("transfer_out", amount, context)
        return min(MAX_INDEX, flags_score + amount_score)


    def risk_of_drop(self, in_data_of_susp_acc: bool) -> int:
        # Список ведётся вручную только для подтверждённых случаев.
        # Это сильный сигнал, а не постепенная оценка поведения.
        return 100 if in_data_of_susp_acc else 0
    

    def transfer(self, other: "Account", amount: int, context: OperationContext):
        ensure_new_operation(context)
        data_of_operations.add(context.operation_id)
        if context.channel != "SBP":
            raise ValueError("перевод должен проходить через СБП")
        if self is other:
            raise BankException("нельзя переводить на тот же самый счёт")
        if amount <= 0:
            self.record_operation("transfer_out", amount, context, other.id, status="blocked")
            other.record_operation("transfer_in", amount, context, self.id, status="blocked")
            raise ValueError("сумма должна быть положительной")
        now = context.occurred_at
        risk_flags = [False] * 7
        if amount > self.balance:
            self.record_operation("transfer_out", amount, context, other.id, status="blocked")
            other.record_operation("transfer_in", amount, context, self.id, status="blocked")
            raise ValueError("недостаточно средств")
        if other.id == self.id:
            other.balance += amount
            self.balance -= amount
            if context.channel == "SBP" and self.bank_id != other.bank_id:
                other.transf_from_another_bank.append((amount, now))
            self.record_operation("transfer_out", amount, context, other.id)
            other.record_operation("transfer_in", amount, context, self.id)
            return
        if other.id in data_of_susp_acc:
            risk_flags[0] = True
        if context.device_id in data_of_susp_devices:
            risk_flags[1] = True
        if is_within_window(self.last_susp_activity, now, timedelta(hours=6)):
            risk_flags[2] = True
        if is_within_window(self.last_data_change, now, timedelta(days=2)):
            risk_flags[3] = True
        risk_flags[4] = context.payment_network_risk
        self_transf_from_another_bank_sum_24h = client_self_sbp_sum_24h(self.id, now)
        if (self_transf_from_another_bank_sum_24h > 20000000
            and other.is_indiv
            and not client_had_recent_relation(self.id, other.id, now)):
            risk_flags[5] = True
        if other.susp_ind >= susp_threshold:
            risk_flags[6] = True
        risk = self.risk_of_transfer(risk_flags, amount, context)
        self.anx_ind = add_index_points(self.anx_ind, risk)
        drop_risk = other.risk_of_drop(other.id in data_of_susp_acc)
        other.susp_ind = add_index_points(other.susp_ind, drop_risk)
        if self.anx_ind >= risk_threshold:
            self.record_operation("transfer_out", amount, context, other.id, status="blocked")
            other.record_operation("transfer_in", amount, context, self.id, status="blocked")
            raise BankException("подозрительный перевод заблокирован: " \
            "клиент может быть обманут")
        if other.susp_ind >= susp_threshold:
            self.record_operation("transfer_out", amount, context, other.id, status="blocked")
            other.record_operation("transfer_in", amount, context, self.id, status="blocked")
            raise BankException("подозрительный перевод заблокирован: ненадёжный получатель")
        self.balance -= amount
        other.balance += amount
        self.recipients[other.id] = now
        other.transfers_to_acc[self.id] = now
        self.record_operation("transfer_out", amount, context, other.id)
        other.record_operation("transfer_in", amount, context, self.id)
        self.sum_per_day[-1] += amount
        if other.is_abroad and other.is_indiv and amount > 10000000:
            self.last_big_cross_boarder_pay = now


    def withdrawing_risk(self, risk_flags: list[bool], amount: int, context: OperationContext) -> int:
        flags_score = score_flags(risk_flags, WITHDRAWAL_WEIGHTS)
        amount_score = self._amount_anomaly_points(
            "cash_withdrawal", amount, context
        )
        return min(MAX_INDEX, flags_score + amount_score)
    

    def withdrawing(self, amount: int, pin: str, context: OperationContext):  # снятие через банкомат
        ensure_new_operation(context)
        data_of_operations.add(context.operation_id)
        if context.channel != "ATM":
            self.record_operation("cash_withdrawal", amount, context, status="blocked")
            raise ValueError("снятие наличных должно проходить через ATM")
        if amount <= 0:
            self.record_operation("cash_withdrawal", amount, context, status="blocked")
            raise ValueError("сумма должна быть положительной")
        now = context.occurred_at
        if pin != self.pin:
            self.record_operation("cash_withdrawal", amount, context, status="blocked")
            self.count_refuses_to_prov_cash += 1
            raise BankException("неверный пин-код")
        if amount > self.balance:
            self.record_operation("cash_withdrawal", amount, context, status="blocked")
            self.count_refuses_to_prov_cash += 1
            raise BankException("недостаточно средств")
        risk_flags = [False] * 7
        if is_within_window(self.last_susp_activity, now, timedelta(hours=6)):
            risk_flags[0] = True
        if is_within_window(self.last_data_change, now, timedelta(days=2)):
            risk_flags[1] = True
        risk_flags[2] = context.payment_network_risk
        self_transf_from_another_bank_sum_24h = client_self_sbp_sum_24h(self.id, now)
        has_recent_fin_event = is_within_window(
            last_fin_events.get(self.id),
            now,
            timedelta(hours=24),
        )
        if has_recent_fin_event or self_transf_from_another_bank_sum_24h > 20_000_000:
            risk_flags[3] = True
        if self.count_refuses_to_prov_cash >= 5:
            risk_flags[4] = True
        risk_flags[5] = has_apdu_risk(context)
        if context.device_id in data_of_susp_devices:
            risk_flags[6] = True
        risk = self.withdrawing_risk(risk_flags, amount, context)
        self.anx_ind = add_index_points(self.anx_ind, risk)
        drop_risk = self.risk_of_drop(self.id in data_of_susp_acc)
        self.susp_ind = add_index_points(self.susp_ind, drop_risk)
        if self.anx_ind >= risk_threshold:
            self.record_operation("cash_withdrawal", amount, context, status="blocked")
            raise BankException("возможно, клиент обманут")
        if self.susp_ind >= susp_threshold:
            self.record_operation("cash_withdrawal", amount, context, status="blocked")
            raise BankException("возможно, клиент нарушает закон")
        self.balance -= amount
        self.record_operation("cash_withdrawal", amount, context)
        self.sum_per_day[-1] += amount


    def drop_risk_in_top_up(self):
        # Метод вызывается только если уже выполнено всё составное условие:
        # физлицо + токенизированная карта + перевод физлицу за границу
        # более 100 000 ₽ в предыдущие 24 часа.
        return 60


    def risk_in_top_up(self, amount: int, context: OperationContext):
        flags = [
            context.payment_network_risk,
            has_apdu_risk(context),
            context.device_id in data_of_susp_devices,
        ]
        flags_score = score_flags(flags, TOP_UP_WEIGHTS)
        amount_score = self._amount_anomaly_points(
            "cash_deposit", amount, context
        )
        return min(MAX_INDEX, flags_score + amount_score)


    def top_up(self, amount: int, pin: str, is_tokenize: bool, context: OperationContext):    # пополнение через банкомат
        ensure_new_operation(context)
        data_of_operations.add(context.operation_id)
        if context.channel != "ATM":
            self.record_operation("cash_deposit", amount, context, status="blocked")
            raise ValueError("пополнение наличными должно проходить через ATM")
        if amount <= 0:
            self.record_operation("cash_deposit", amount, context, status="blocked")
            raise ValueError("сумма должна быть положительной")
        now = context.occurred_at
        if pin != self.pin:
            self.record_operation("cash_deposit", amount, context, status="blocked")
            raise BankException("неверный пин-код")
        self.anx_ind = add_index_points(
            self.anx_ind, self.risk_in_top_up(amount, context)
        )
        recent_cross_border_payment = any(
            is_within_window(
                account.last_big_cross_boarder_pay,
                now,
                timedelta(hours=24),
            )
            for account in data_of_acc[self.id].values()
        )
        if self.is_indiv and is_tokenize and recent_cross_border_payment:
            self.susp_ind = add_index_points(
                self.susp_ind, self.drop_risk_in_top_up()
            )
        if self.anx_ind >= risk_threshold:
            self.record_operation("cash_deposit", amount, context, status="blocked")
            raise BankException("возможно, клиент обманут")
        if self.susp_ind >= susp_threshold:
            self.record_operation("cash_deposit", amount, context, status="blocked")
            raise BankException("возможно, клиент нарушает закон")
        self.balance += amount
        self.record_operation("cash_deposit", amount, context)


    def risk_of_card_purchase(
        self,
        risk_flags: list[bool],
        amount: int,
        merchant_id: int,
        context: OperationContext,
    ) -> int:
        flags_score = score_flags(risk_flags, CARD_WEIGHTS)
        amount_score = self._amount_anomaly_points(
            "card_purchase", amount, context, peer_id=merchant_id
        )
        return min(MAX_INDEX, flags_score + amount_score)


    def card_purchase(
        self,
        amount: int,
        merchant_id: int,
        context: OperationContext,
    ) -> None:
        ensure_new_operation(context)
        data_of_operations.add(context.operation_id)
        if context.channel != "CARD":
            self.record_operation(
                "card_purchase", amount, context, merchant_id, status="blocked"
            )
            raise ValueError("покупка должна проходить по каналу CARD")
        if amount <= 0:
            self.record_operation(
                "card_purchase", amount, context, merchant_id, status="blocked"
            )
            raise ValueError("сумма должна быть положительной")
        if amount > self.balance:
            self.record_operation(
                "card_purchase", amount, context, merchant_id, status="blocked"
            )
            raise BankException("недостаточно средств")
        risk_flags = [
            context.device_id in data_of_susp_devices,
            context.payment_network_risk,
        ]
        risk = self.risk_of_card_purchase(risk_flags, amount, merchant_id, context)
        self.anx_ind = add_index_points(self.anx_ind, risk)
        if self.anx_ind >= risk_threshold:
            self.record_operation(
                "card_purchase", amount, context, merchant_id, status="blocked"
            )
            raise BankException("покупка по карте заблокирована")
        self.balance -= amount
        self.sum_per_day[-1] += amount
        self.record_operation(
            "card_purchase", amount, context, merchant_id, status="completed"
        )


    def end_of_the_day(self, time: datetime) -> None:
        now = time
        if self.last_index_decay_at is None:
            self.last_index_decay_at = now
        elif now > self.last_index_decay_at:
            elapsed = now - self.last_index_decay_at
            self.anx_ind = decay_anx_index(self.anx_ind, elapsed)
            self.susp_ind = decay_susp_index(self.susp_ind, elapsed)
            self.last_index_decay_at = now
        self.sum_per_day.append(0)
        cutoff = now - timedelta(days=180)
        self.operation_history = deque(
            record
            for record in self.operation_history
            if record.context.occurred_at >= cutoff
        )
        for recipient, event_at in list(self.recipients.items()):
            if event_at + timedelta(days=180) < now:
                del self.recipients[recipient]
        for sender, event_at in list(self.transfers_to_acc.items()):
            if event_at + timedelta(days=180) < now:
                del self.transfers_to_acc[sender]
        self.count_refuses_to_prov_cash = 0


def end_of_the_day_for_all(time: datetime) -> None:
    for account in (acc for self_accs in data_of_acc.values() for acc in self_accs.values()):
        account.end_of_the_day(time)
    data_of_operations.clear()


def add_to_data_of_susp_acc(id: int):
    data_of_susp_acc.add(id)


def discard_from_data_of_susp_acc(id: int):
    data_of_susp_acc.discard(id)


def add_to_data_of_susp_devices(id: int):
    data_of_susp_devices.add(id)


def discard_from_data_of_susp_devices(id: int):
    data_of_susp_devices.discard(id)


def add_account(
    id: int, acc_id: int, balance: int, bank_id: int,
    pin: str, is_abroad: bool, is_indiv: bool,
) -> Account:
    return Account(id, acc_id, balance, bank_id, pin, is_abroad, is_indiv)


def delete_account(id: int, acc_id: int):
    del data_of_acc[id][acc_id]


def set_fin_event(id: int, time: datetime):
    if id not in last_fin_events or last_fin_events[id] < time:
        last_fin_events[id] = time


def transfer(self_id: int, self_acc_id: int, other_id: int, 
             other_acc_id: int, amount: int, context: OperationContext):
    if self_id == other_id and self_acc_id == other_acc_id:
        raise BankException("нельзя перевести на тот же самый счёт")
    data_of_acc[self_id][self_acc_id].transfer(data_of_acc[other_id][other_acc_id], amount, context)


def withdrawing(self_id: int, self_acc_id: int, amount: int, pin: str, context: OperationContext):
    data_of_acc[self_id][self_acc_id].withdrawing(amount, pin, context)


def top_up(self_id: int, self_acc_id: int, amount: int, 
           pin: str, is_tokenize: bool, context: OperationContext):
    data_of_acc[self_id][self_acc_id].top_up(amount, pin, is_tokenize, context)


def card_purchase(self_id: int, self_acc_id: int, 
                  amount: int, merchant_id: int, context: OperationContext):
    data_of_acc[self_id][self_acc_id].card_purchase(amount, merchant_id, context)


def _update_last_data_change(account: Account, time: datetime) -> None:
    last_time = account.last_data_change
    if last_time is None or last_time < time:
        account.last_data_change = time


def new_device(self_id: int, self_acc_id: int, id: int, time: datetime) -> None:
    if id in data_of_susp_devices:
        raise BankException("устройство из списка мошеннических")
    account = data_of_acc[self_id][self_acc_id]
    account.devices.add(id)
    _update_last_data_change(account, time)


def susp_activity(self_id: int, self_acc_id: int, time: datetime) -> None:
    account = data_of_acc[self_id][self_acc_id]
    last_time = account.last_susp_activity
    if last_time is None or last_time < time:
        account.last_susp_activity = time


def data_change(self_id: int, self_acc_id: int, time: datetime) -> None:
    account = data_of_acc[self_id][self_acc_id]
    _update_last_data_change(account, time)


def set_anx_index(self_id: int, self_acc_id: int, value: int):
    if not 0 <= value <= 100:
        raise ValueError("невозможное значение")
    data_of_acc[self_id][self_acc_id].anx_ind = value


def set_susp_index(self_id: int, self_acc_id: int, value: int):
    if not 0 <= value <= 100:
        raise ValueError("невозможное значение")
    data_of_acc[self_id][self_acc_id].susp_ind = value
