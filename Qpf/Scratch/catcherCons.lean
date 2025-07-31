import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Const
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Fix
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Qpf.Qpf.Multivariate.Constructions.DeepThunk
import Qpf.Util.Vec
import Qpf.Builtins.List
import Qpf.Macro.Data
import Qpf.Macro.Comp

open MvQPF

instance { F : TypeFun n.succ } { α : TypeVec n} [inst : MvFunctor F] [MvQPF F] : Coe ((Cofix F) α) (DeepThunk.Uncurried F (α ::: β)) where
  coe := DeepThunk.inject

codata QR α
  | cons (hd : α) (tl : List (QR α))
abbrev QRX := DeepThunk QR.Base.Uncurried
def QRX.cons (hd : α) (tl : List (β ⊕ QRX α β)) : DeepThunk QR.Base.Uncurried α β := MvQPF.Cofix.mk (.cons hd tl)

def QR.gcorec (f : β → QRX α β) : β → QR α :=
  (MvQPF.Cofix.corec (match MvQPF.Cofix.dest · with
    | .cons hd (ls : List (DTSum β (QRX α β))) =>
      let ls : @TypeFun.ofCurried 1 List ![DTSum β (QRX α β)] := ls
      let tl : @TypeFun.ofCurried 1 List ![QRX α β] := (MvFunctor.map (fun | 0 => uniform) ls)
      .cons hd tl
  )) ∘ f
  where uniform | DTSum.recall x => f x | .cont x => x

codata QT α β
  | lf (v : α)
  | br (v : β) (l r : QT α β)

namespace QT
codata QC α
  | node (v : α) : QT α (QC α) → QC α

def QCX.node (v : α) (tl : QT α (β ⊕ QC.DeepThunk α β)) : QC.DeepThunk α β := MvQPF.Cofix.mk (.node v tl)

end QT

codata QLs α
  | cons (hd : α) (tl : QLs α)
  | nil

def QLs.gcorec (f : β → QLs.DeepThunk α β) : β → QLs α :=
  (MvQPF.Cofix.corec (match MvQPF.Cofix.dest · with
    | .nil => .nil
    | .cons hd x => .cons hd (uniform x)
    )) ∘ f
  where uniform | .recall x => f x | .cont x => x

def natsFrom : ℕ → QLs ℕ := QLs.gcorec fun v => .cons v (.recall (v + 1))

def extConstDemo : α → QLs ℕ := QLs.gcorec fun _ => natsFrom 0

/- codef double : QLs α → QLs α  -/
/-   | .nil => .nil -/
/-   | .cons hd tl => .cons hd (.cons hd (double tl)) -/

/- def skipEven : QLs α → QLs α := _ -/

def double : QLs α → QLs α := QLs.gcorec (match MvQPF.Cofix.dest · with
  | .nil => .nil
  /- | .cons hd tl => .cons hd $ .recall $ .cons hd tl) -/
  | .cons hd tl => .cons hd $ .cont $ .cons hd $ .recall tl)

/- def flatten : QLs (QLs α) → QLs α := -/
/-   QLs.gcorec (β := QLs (QLs α)) (match MvQPF.Cofix.dest · with -/
/-     | .nil => .nil -/
/-     | .cons hd tl => match MvQPF.Cofix.dest hd with -/
/-       | .nil => sorry -/
/-       | .cons hd tl => sorry) -/

/- codef f ... -/
/-   | ... => -/
/-     .cons _ <| -/
/-       let x := f ... -/
/-       match x.dest with -/
/-         | ... => ... -/

/- codef doubleOdd (x : QLs α)  -/
/-   | .nil => .nil -/
/-   | .cons hd tl => .cons hd (.cons hd (doubleOdd (skipEven tl))) -/

def countDown : QLs ℕ → QLs ℕ := QLs.DeepThunk.corec (match MvQPF.Cofix.dest · with
  | .nil => .nil
  | .cons (hd : ℕ) tl =>
    let rec f := fun
      | 0 => .cons 0 $ .recall tl
      | n + 1 => .cons (n + 1) $ .cont (f n)
    f hd
  )

def merge : QLs α × QLs α → QLs α :=
  QLs.DeepThunk.corec (fun ⟨a, b⟩ => match MvQPF.Cofix.dest a with
    | .cons hd a => .cons hd $ .recall (b, a)
    | .nil => b)

codata S α | node : α → S α → S α

def take : ℕ → QLs α → List α
  | 0, _ => []
  | n + 1, v => match MvQPF.Cofix.dest v with
    | .nil => []
    | .cons hd tl => hd :: (take n tl)

def double' (x : QLs α) : QLs α := @QLs.corec _ ((QLs.Base α (QLs α)) ⊕ QLs α)
  (fun
    | .inl b  => match b with 
      | .cons hd tl => .cons hd (Sum.inr tl)
      | .nil        => .nil
    | .inr xs => match xs.dest with 
      | .cons hd tl => .cons hd (Sum.inl (.cons hd tl))
      | .nil        => .nil)
  (.inr x)

def skipEveryN (n : ℕ) : QLs α → QLs α :=
  QLs.DeepThunk.corec (
    let rec f tl
      | n+1 => match Cofix.dest tl with
        | .cons _ tl => f tl n
        | .nil => .nil
      | 0 => tl

    match Cofix.dest · with
    | .cons hd tl => .cons hd $ .recall $ f tl (n - 1)
    | .nil => .nil)

def sieve : QLs ℕ → QLs ℕ :=
  QLs.DeepThunk.corec (match Cofix.dest · with
    | .cons hd tl => .cons hd $ .cont $ skipEveryN hd tl
    | .nil => .nil)

namespace s

codata Stream α
  | cons (hd : α) (tl : Stream α)

#print Stream.cons

def skip (n : ℕ) : Stream α → Stream α :=
  Stream.DeepThunk.corec (fun v =>
    let rec f v
      | 0 => v
      | n+1 => match MvQPF.Cofix.dest v with
        | .cons (hd : α) (tl : Stream α) => f tl n
    f v n
  )

/- def repN (n : ℕ) : Stream α → Stream α := -/
/-   Stream.DeepThunk.corec (match Cofix.dest · with -/
/-     | .cons (hd : α) (tl : Stream α) => -/
/-       let rec f -/
/-         | 0 | 1 => .cons hd (.inl tl) -/
/-         | n+1 => .cons hd (.inr (f n)) -/
/-       f n) -/

/- codef skip : ℕ → Stream α → Stream α -/
/-   | 0, .cons hd tl | 1, .cons hd tl => .cons hd tl -/
/-   | n+1, .cons hd tl => (skip n (.cons hd tl)) -/

def take : ℕ → Stream α → List α
  | 0, _ => []
  | n + 1, v => match MvQPF.Cofix.dest v with
    | .cons hd tl => hd :: (take n tl)

def natsFrom : ℕ → Stream ℕ := Stream.DeepThunk.corec fun v => .cons v (.recall (v + 1))


/- codef allNatsCursed : CoList ℕ := .cons 0 (CoList.map (Nat.succ) allNatsCursed) -/
def allNatsCursed : Stream ℕ := Stream.DeepThunk.corec (fun v => sorry) ()

/- #eval take 10 $ repN 5 $ natsFrom 0 -/

end s

#print prefix s

/- #eval take 2 $ sieve $ natsFrom 2 -/
/- #eval (take 10 $ natsFrom 2) -/
