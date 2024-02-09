import Mathlib.Data.QPF.Multivariate.Basic

variable {n} {P : MvPFunctor n} 

instance : MvFunctor P := by infer_instance
instance : MvQPF P := {
  P := P,
  abs := id,
  repr := id,
  abs_repr := by intros; rfl,
  abs_map := by intros; rfl,
}
