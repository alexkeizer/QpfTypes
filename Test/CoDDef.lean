import Qpf.Macro.Data
import Qpf.Macro.Datadef
import Qpf.Builtins.List

import Mathlib.Data.QPF.Multivariate.Constructions.Cofix


codata CoList α where
  | cons : α → CoList α → CoList α
  | nil

set_option trace.QPF true
set_option pp.rawOnError true

def nats : CoList Nat
  := CoList.corec (fun n => .cons n (n + 1)) 0

variable (hello : Nat)

def allUnit : CoList Unit := CoList.corec (fun _ => .cons () ()) ()

codef au1 : CoList Unit := .cons () au1
codef au2 : CoList Unit := .cons () allUnit
codef au3 : CoList Unit := .cons () (.cons () au3)
codef succAfter (n : ℕ) : CoList ℕ :=
  .cons n (succAfter (n + 1))

codata CoRose α where
  | node : α → CoList (CoRose α) → CoRose α

def az : ℕ → ℕ := fun a => match a with
  | 0 => 0
  | n+1 => az n

def add {a : ℕ} (b : ℕ) := a + b

codef auR : CoRose Unit := .node () (.cons (auR) .nil)

codef skipn (n : ℕ) (s : CoList ℕ) : CoList ℕ := match n, MvQPF.Cofix.dest s with
  | _, .nil => .nil
  | 0, .cons hd tl => .cons hd tl
  | n+1, .cons hd tl => skipn n tl

/- example : ℕ → CoList ℕ := -/
/-   let rec succAfter (n : ℕ) :CoList ℕ := .cons n (succAfter (n + 1)) -/
/-   succAfter -/

/- def nats' := succAfter 0 -/

def CoList.map (f : α → β) (i : CoList α) : CoList β :=
  CoList.corec (fun i =>
      match MvQPF.Cofix.dest i with
      | .nil => .nil
      | .cons hd tl => .cons (f hd) tl)
    i

def CoList.dobble (i : CoList α) : CoList α :=
  CoList.DeepThunk.corec (fun i =>
      match MvQPF.Cofix.dest i with
      | .nil => .nil
      | .cons hd tl => .cons hd $ .cont $ .cons hd $ .recall tl
      )
    i

codef CoList.map' {α β : Type _} (f : α → β) (ls : CoList α) : CoList β := match MvQPF.Cofix.dest ls with
  | .nil => .nil
  | .cons (hd : α) (tl : CoList α) => .cons (f hd) (CoList.map' f tl)

/- codef allNatsCursed : CoList ℕ := .cons 0 (CoList.map (Nat.succ) allNatsCursed) -/

codef map' {α β} (f : α → β) (ls : CoList α) : CoList β := match ls with
  | .cons _ _ => .cons (f hd) (map' f tl)

codef CoList.map' (f : α → β) : CoList α → CoList β
  | .cons hd tl => .cons (f hd) (CoList.map f tl)

codef CoList.dobble' : CoList α → CoList β
  | .cons hd tl => .cons hd (.cons hd (CoList.dobble tl))

