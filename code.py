from datetime import UTC, datetime, timedelta
from collections import deque
from dataclasses import dataclass


data_of_susp_acc: set[int] = set()
data_of_susp_devices: set[int] = set()
data_of_acc: dict[int, list["Account"]] = dict()
last_fin_events: dict[int, datetime] = dict()
risk_threshold: int = 
susp_threshold: int = 


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


def has_apdu_risk(operation: OperationContext) -> bool:
    return (
        operation.channel == "ATM"
        and operation.apdu_response_ms is not None
        and operation.apdu_limit_ms is not None
        and operation.apdu_response_ms > operation.apdu_limit_ms
    )


class Account:
    def __init__(self, id: int, balance: int, bank_id: int, pin: str, is_abroad: bool, is_indiv: bool):
        self.anx_ind: int = 0   # индекс тревожности
        self.susp_ind: int = 0  # индекс подозрительности
        self.id: int = id   # id пользователя
        self.bank_id = bank_id  # id банка
        self.is_indiv = is_indiv    # клиент физлицо или нет
        self.pin: str = pin # пин-код
        self.balance: int = balance # баланс
        self.average_pay_per_day: int = 0   # средняя трата за день
        self.devices: set[int] = set()  # устройства
        self.recipients: dict[int, datetime] = dict()   # получатели за последние 180 дней
        self.transfers_to_acc: dict[int, datetime] = dict() # отправители за последние 180 дней
        self.pays_per_day: dict[int, int] = dict()  # кому сколько отправил за последний день
        self.sum_per_day: deque[int] = deque([0], maxlen=180)    # траты за последние 180 дней
        self.last_susp_activity: datetime | None = None # дата последней подозрительной активности
        self.last_data_change: datetime | None = None # последние изменения данных
        self.transf_from_another_bank_sum_per_day: int = 0     # сумма переводов из другого банка за календарный день
        self.transf_from_another_bank: deque[tuple[int, datetime]] = deque()    # свои переводы из другого банка за последние 24 часа
        self.last_big_cross_boarder_pay: datetime | None = None # последний крупный перевод за границу
        self.count_refuses_to_prov_cash: int = 0    # количество отказов в снятии средств за день
        self.is_abroad: bool = is_abroad    # зарубежный ли счёт
        data_of_acc.setdefault(id, []).append(self)


    def risk_of_transfer(self, risk_flags: list[bool], sum: int) -> int:
        raise NotImplementedError


    def risk_of_drop(self) -> int:
        raise NotImplementedError
    

    def transfer(self, other: "Account", amount: int, context: OperationContext):
        if amount <= 0:
            raise ValueError("сумма должна быть положительной")
        now = context.occurred_at
        risk_flags = [False] * 7
        if amount > self.balance:
            raise ValueError("недостаточно средств")
        if other.id == self.id:
            other.balance += amount
            self.balance -= amount
            if context.channel == "SBP" and self.bank_id != other.bank_id:
                other.transf_from_another_bank.append((amount, now))
            return
        if other.id in data_of_susp_acc:
            risk_flags[0] = True
        if context.device_id in data_of_susp_devices:
            risk_flags[1] = True
        if self.last_susp_activity is not None and self.last_susp_activity + timedelta(hours=6) >= now:
            risk_flags[2] = True
        if self.last_data_change is not None and self.last_data_change + timedelta(days=2) >= now:
            risk_flags[3] = True
        risk_flags[4] = context.payment_network_risk
        while self.transf_from_another_bank and self.transf_from_another_bank[0][1] + timedelta(hours=24) <= now:
            self.transf_from_another_bank.popleft()
        self.transf_from_another_bank_sum_per_day = sum(amount_kop for amount_kop, _ in self.transf_from_another_bank)
        if (self.transf_from_another_bank_sum_per_day > 20000000
            and other.is_indiv
            and other.id not in self.recipients 
            and other.id not in self.transfers_to_acc):
            risk_flags[5] = True
        if other.susp_ind >= susp_threshold:
            risk_flags[6] = True
        risk = self.risk_of_transfer(risk_flags, amount)
        self.anx_ind += risk
        drop_risk = other.risk_of_drop()
        other.susp_ind += drop_risk
        if self.anx_ind >= risk_threshold:
            raise Exception("подозрительный перевод заблокирован: " \
            "клиент может быть обманут")
        if other.susp_ind >= susp_threshold:
            raise Exception("подозрительный перевод заблокирован: ненадёжный получатель")
        self.balance -= amount
        other.balance += amount
        self.recipients[other.id] = now
        other.transfers_to_acc[self.id] = now
        if other.id in self.pays_per_day:
            self.pays_per_day[other.id] += amount
        else:
            self.pays_per_day[other.id] = amount
        self.sum_per_day[-1] += amount
        if other.is_abroad and other.is_indiv and amount > 10000000:
            self.last_big_cross_boarder_pay = now


    def withdrawing_risk(self, risk_flags: list[bool], amount: int) -> int:
        raise NotImplementedError
    

    def withdrawing(self, amount: int, pin: str, context: OperationContext):  # снятие через банкомат
        if amount <= 0:
            raise ValueError("сумма должна быть положительной")
        now = context.occurred_at
        if pin != self.pin:
            self.count_refuses_to_prov_cash += 1
            raise Exception("неверный пин-код")
        if amount > self.balance:
            self.count_refuses_to_prov_cash += 1
            raise Exception("недостаточно средств")
        risk_flags = [False] * 7
        if self.last_susp_activity is not None and self.last_susp_activity + timedelta(hours=6) >= now:
            risk_flags[0] = True
        if self.last_data_change is not None and self.last_data_change + timedelta(days=2) >= now:
            risk_flags[1] = True
        risk_flags[2] = context.payment_network_risk
        while self.transf_from_another_bank and self.transf_from_another_bank[0][1] + timedelta(hours=24) <= now:
            self.transf_from_another_bank.popleft()
        self.transf_from_another_bank_sum_per_day = sum(amount_kop for amount_kop, _ in self.transf_from_another_bank)
        if (self.id in last_fin_events and last_fin_events[self.id] + timedelta(hours=24) >= now
            or self.transf_from_another_bank_sum_per_day > 20000000):
            risk_flags[3] = True
        if self.count_refuses_to_prov_cash >= 5:
            risk_flags[4] = True
        risk_flags[5] = has_apdu_risk(context)
        if context.device_id in data_of_susp_devices:
            risk_flags[6] = True
        risk = self.withdrawing_risk(risk_flags, amount)
        self.anx_ind += risk
        drop_risk = self.risk_of_drop()
        self.susp_ind += drop_risk
        if self.anx_ind >= risk_threshold:
            raise Exception("возможно, клиент обманут")
        if self.susp_ind >= susp_threshold:
            raise Exception("возможно, клиент нарушает закон")
        self.balance -= amount
        self.sum_per_day[-1] += amount


    def drop_risk_in_top_up(self, sum: int):
        raise NotImplementedError


    def risk_in_top_up(self, sum: int, context: OperationContext):
        raise NotImplementedError


    def top_up(self, amount: int, pin: str, is_tokenize: bool, context: OperationContext):    # пополнение через банкомат
        if amount <= 0:
            raise ValueError("сумма должна быть положительной")
        now = context.occurred_at
        if pin != self.pin:
            raise Exception("неверный пин-код")
        self.anx_ind += self.risk_in_top_up(amount, context)
        if (self.is_indiv and is_tokenize and any(cross_boarder is not None and 
            cross_boarder + timedelta(hours=24) >= now for 
            cross_boarder in [acc.last_big_cross_boarder_pay for acc in data_of_acc[self.id]])):
            self.susp_ind += self.drop_risk_in_top_up(amount)
        if self.anx_ind >= risk_threshold:
            raise Exception("возможно, клиент обманут")
        if self.susp_ind >= susp_threshold:
            raise Exception("возможно, клиент нарушает закон")
        
        self.balance += amount


    def end_of_the_day(self):
        self.average_pay_per_day = sum(self.sum_per_day) // len(self.sum_per_day)
        self.sum_per_day.append(0)
        for recipient in list(self.recipients.keys()):
            if self.recipients[recipient] + timedelta(days=180) < datetime.now(UTC):
                del self.recipients[recipient]
        for transfer in list(self.transfers_to_acc.keys()):
            if self.transfers_to_acc[transfer] + timedelta(days=180) < datetime.now(UTC):
                del self.transfers_to_acc[transfer]
        self.pays_per_day.clear()
        self.count_refuses_to_prov_cash = 0


    def new_device(self, id: int):
        if id in data_of_susp_devices:
            raise Exception("устройство из списка мошеннических")
        self.devices.add(id)
        self.last_data_change = datetime.now(UTC)


    def susp_activity(self):
        self.last_susp_activity = datetime.now(UTC)


    def data_change(self):
        self.last_data_change = datetime.now(UTC)


    def set_anx_index(self, value):
        self.anx_ind = value


    def set_susp_index(self, value):
        self.susp_ind = value


    

    
    
        
