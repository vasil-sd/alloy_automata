module example

open util/ordering[Time]
open automaton[Email, Time, Stage, Cond, StartStage, FinalStage]

-- небольшой пример использования Automaton
-- автомат простой:
-- приходит письмо и нам нужно определить его тип
-- соответственно письмо проходит через несколько 
-- состояний, где оно классифицироуется, как принадлежащие
-- какой-либо категории (см. диаграмму)

sig Time {}

-- тут типы писем
enum EmailType {
  Unknown,
  Normal,
  Spam
}

sig ValidTypes = Normal + Spam {}

-- Email - это у нас базовое общее множество писем
abstract sig Email {
   Type: EmailType -> Time -- тип будет определён в процессе обработки
}

-- тут задаём непересекающиеся 
-- подмножества множества Email
sig NormalEmails extends Email  {}
sig SpamEmails extends  Email {}
sig UnknownEmails extends Email {}

-- состояния автомата
enum Stage {
Receiving, --тут принимаем письмо в начальный момент времени
CheckSpam, 
CheckNormal,
Success, -- это конечное состояние, когда нам удалось определить тип письма
Fail -- это конечное состояние, когда тип письма мы не смогли определить
}

sig StartStage = Receiving {}
sig FinalStage = Success + Fail {}

-- атомарные предикаты на дугах автомата
enum Cond {
Detected,
NotDetected
}

-- таблица переходов автомата
-- (чтобы нормально отображалась в редакторе,
--  советую поставить моноширинный шрифт, например
--  DejaVu Sans Mono)

one sig Transitions {
--     Predicate             From                To
-------------------------------------------------------------------
  Tr : Cond               -> Stage            -> Stage
}{
  Tr = 
       Detected           -> CheckSpam        -> Success          +
       Detected           -> CheckNormal      -> Success          +

       NotDetected        -> Receiving        -> CheckSpam        +
       NotDetected        -> CheckSpam        -> CheckNormal      +
       NotDetected        -> CheckNormal      -> Fail
}

-- тут задаём предикат, что в начальный момент времени
-- у принимаемого письма тип неизвестен
pred Initial {
    all eml : Email {
        eml.Type.first = Unknown
        eml.Predicates[first] = NotDetected
    }
}

-- тут зададим предикаты проверок
pred CheckAction[s : Stage, emls: Email, type : EmailType] {
	all t : Time - first {
    -- для всех моментов времени
        all eml : Email {
        -- для каждого письма
            (eml.State[t] = s and eml in emls) implies {
            -- если письмо в соотв. подмножестве то ставим признак детекции
            -- и соотв тип, считаем, что мы его определили
                eml.Predicates[t] = Detected
                all future : Time {
                    gte[future, t] implies eml.Type.future = type
                }
            }
            -- письмо в множестве но не на соотв стадии обработки
            -- тип не меняется
            -- NB: в аллой нужно обязательно писать предикаты для сохранения
            -- данных в негативных случаях, иначе аллой в этом месте будет перебирать
            -- все возможные варианты, что для новичком может быть весьма удивительным эффектом
            (eml in emls and not eml.State[t] = s) implies {
                eml.Type.t = eml.Type.(t.prev)
            }
            -- если на данной стадии детекции не наше письмо, то ставим NotDetected предикат
            (eml.State[t] = s and eml not in emls) implies {
                eml.Predicates[t] = NotDetected
            }
        }
    }
}

-- общий предикат для детекции типов писем
pred Detection {
  CheckAction[CheckSpam, SpamEmails, Spam]
  CheckAction[CheckNormal, NormalEmails, Normal]
}

-- тут сам процесс автомата определения типов писем
pred Process {
    -- подключаем пердикат автомата
    Transitions.Tr.Automaton

    -- начальные состояния принимаемых писем
    Initial

    -- предикат детекции типов писем
    Detection
}

-- докажем тут, что если тип письма определим в принципе, то
-- у нас должны все письма определяться всегда
Type_Is_Always_Detected_For_Detectable_Emails:
check { 
    (no UnknownEmails and Process)
    implies {
       -- на последний момент времени типы всех писем определены
       all eml : Email {
          eml.Type.last in ValidTypes
       }
    }
} for 10

-- тут примеры обработки писем
-- при просмотре советую использовать пресет для визуализации, который лежит рядом с данным файлом
One_Normal_Email: run { Process } for 10 Time, exactly 1 NormalEmails, 0 SpamEmails, 0 UnknownEmails
One_Spam_Email: run { Process } for 10 Time, 0 NormalEmails, exactly 1 SpamEmails, 0 UnknownEmails
One_Undetected_Email: run { Process } for 10 Time, 0 NormalEmails, 0 SpamEmails, exactly 1 UnknownEmails
One_Spam_One_Undetected_Email: run { Process } for 10 Time, 0 NormalEmails, exactly 1 SpamEmails, exactly 1 UnknownEmails
