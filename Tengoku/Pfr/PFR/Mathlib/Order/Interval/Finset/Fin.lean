module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

public section

open Finset

namespace Fin

lemma Iio_succ_eq_Iic_castSucc {n : ℕ} (k : Fin n) : Iio k.succ = Iic k.castSucc := rfl

end Fin
