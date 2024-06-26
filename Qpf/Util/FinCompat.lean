import Qpf.MathlibPort.Fin2

instance {n} : Coe (Fin n) (Fin2 n) where
  coe x :=
    @Fin2.ofNat' n x.val { h := x.isLt }

instance {n} : Coe (Fin2 n) (Fin n) where
  coe x := by {
    cases n
    · contradiction
    · exact (Fin.ofNat x.toNat)
  }

def toFin2F {n} {α: Type u} (f : Fin  n → α) (x : Fin2 n): α := f x
def toFinF  {n} {α: Type u} (f : Fin2 n → α) (x : Fin  n): α := f x

