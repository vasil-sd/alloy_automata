module automaton[Obj, Time, S, P, InitialS, FinalS]
  -- Obj - сигнатура объектов, которые могут менять состояния
  -- Time - время
  -- S - множество состояний
  -- P - множество атомарных предикатов
  -- InitialS - множество начальных состояний
  -- FinalS - множество конечных состояний

-- Работа автомата моделируется так:
-- для каждого момента времени есть множество активных предикатов
-- и множество текущих (на этот момент времени) состояний.
-- Соответственно множество состояний в следующий момент времени
-- определяется таблицей переходов P -> S -> S.
-- предикат Automaton соотвественно определяет возможные
-- трассы состояний в соотв. с таблицей.

open util/ordering[Time] -- вводим порядок на времени

fact InitialAndFinalStatesInS {
  InitialS in S
  FinalS in S
}

sig State in Obj {
  Predicates : P -> Time, -- задаёт предикаты для 
                          -- моментов времени
  Current : S -> Time
}

fact {
  Obj in State -- для каждого объекта есть State
}

fun Predicates[o : State, t : Time] : set P {
  o.Predicates.t
}

fun State[o : State, t : Time] : S {
  o.Current.t
}

pred Transitions[tr : P -> S -> S] {
  all t: Time - last | -- для каждого момента времени,
                       -- кроме последнего

    let t' = t.next  | -- t' следующий за t

    all s : State    | -- для всех объектов (State <-> Obj)

      let curr_s = s.Current.t   | -- curr_s - состояние объекта
                                   -- в момент времени t

      let next_s = s.Current.t'  | -- состояние объекта в t'

      let preds = s.Predicates.t | -- предикаты допустимых
                                   -- переходов в момент t

      let possible_s = preds.tr[curr_s] | -- возможные будущие
                                          -- состояния

        ( curr_s in FinalS and next_s = curr_s )
          -- ^^ если текущее состояние - конечное, то объект в
          -- нём и остаётся
        or  -- иначе
        some nxt : possible_s | next_s = nxt
          -- берём произвольно какое-нибудь из возможных
          -- будущих состояний и делаем его следующим
          -- актуальным состоянием объекта в момент t'
}

pred Init {
  all s : State |
  some i : InitialS |
    s.Current.first = i
}

pred Final [o : State, t : Time] {
  o.Current.t in FinalS and o.Predicates.t = none
}

pred Automaton[tr : P -> S -> S] {
  Init
  Consistent[tr]
  Transitions[tr]
  all t : Time
  | all o : State
    | let curr_s = o.Current.t
    | let curr_p = o.Predicates.t
    | (some curr_p and curr_p in tr.S.curr_s)
       or
       o.Final[t]
}

pred Consistent[tr : P -> S -> S] {
  -- Есть хоть одно начальное состояние
  some InitialS
  -- начальные и конечные состояния не пересекаются
  no InitialS & FinalS
  -- Если нет исходящих дуг, то это финальное
  -- состояние и наоборот.
  all s : S | no P.tr[s] iff s in FinalS
  -- Если нет входящих дуг, то это только
  -- начальное состояние, обратное, кстати,
  -- неверно.
  all s : S | no P.tr.s => s in InitialS
  -- Нет разных дуг из одного состояния с
  -- одинаковыми предикатами.
  all p : P, s : S | lone p -> s -> S & tr
  -- Один предикат на дугу.
  all s1, s2 : S | lone P -> s1 -> s2 & tr
}
