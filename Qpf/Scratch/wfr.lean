import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Const
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Qpf.Util.Vec
import Qpf.Builtins.List
import Qpf.Macro.Data

inductive hello (α : Type _)
  | a (v : α)
  | b

/- #print prefix MvQPF.Fix -/

/- #print prefix hello -/

set_option trace.QPF true in
data QLs α
  | cons (hd : α) (tl : QLs α)
  | nil

@[simp]
theorem TypeVec.comp_id_append1 {f : α → β} {g : β → γ} {ζ : TypeVec n} :
    TypeVec.comp (@TypeVec.id n ζ ::: g) (@TypeVec.id n _ ::: f)
    = appendFun (@TypeVec.id n _) (g ∘ f) := by
  apply funext₂
  unfold TypeVec.comp
  intro i _
  cases i <;> rfl

theorem TypeVec.append1_injective (h : Function.Injective f) : ∀ i, Function.Injective ((@TypeVec.id n χ ::: f) i) := by
  intro i
  cases i
  <;> simp [TypeVec.appendFun, splitFun]
  · exact h
  · unfold TypeVec.id
    intro _ _ a
    exact a

theorem MvPFunctor.map_inj {P : MvPFunctor n} {f : TypeVec.Arrow α β} 
    (h : ∀ i, Function.Injective (f i)) :
    Function.Injective (P.map f) := by
  rintro ⟨xa, xf⟩ ⟨ya, yf⟩ h_map_eq
  simp [MvPFunctor.map] at h_map_eq
  injection h_map_eq with h1 h2
  subst h1
  simp at h2
  congr 1
  funext i b
  apply h
  show ((f i ∘ _) _ = (f i ∘ _) _)
  /- sorry -/
  unfold TypeVec.comp at h2
  sorry

theorem MvFunctor.map_inj {P : MvFunctor n} {f : TypeVec.Arrow α β}
  (h : ∀ i, Function.Injective (f i))
  : Function.Injective $ P.map f := by
  rintro a b h_eq
  /- simp [MvFunctor.map] at h_eq -/
  sorry

theorem LawfulFunctor.map_inj
    {g} [Nonempty α] [Nonempty (g α)] [G : Functor g] [LG : LawfulFunctor g]
    {f : α → β}
    (h : Function.Injective f) : Function.Injective (Functor.map (f := g) f) := by 
  have : (Function.invFun f) ∘ f = id := by 
    ext x
    simp
    apply Function.leftInverse_invFun (by assumption)
  have :  ∀ x : g α, (Function.invFun f ∘ f) <$> x =  id <$> x := by
    intros x; simp [this]
  have : (G.map (Function.invFun f)) ∘ (G.map f) = G.map id := by
    ext i
    rw [← this]
    simp [LG.comp_map, LG.id_map]
  have : Function.HasLeftInverse (G.map f) := by
    exists (G.map (Function.invFun f))
    simp [Function.LeftInverse]
    intros x
    have : (Functor.map (Function.invFun f) ∘ (Functor.map f)) x = id x := by rw [this, LG.id_map]; simp
    trivial
  exact this.injective

theorem MvQPF.Fix.mk_dest_bij {F} [MvFunctor F] [MvQPF F] : Function.Bijective $ MvQPF.Fix.mk (F := F) (α := α) := by
  apply Function.bijective_iff_has_inverse.mpr
  use MvQPF.Fix.dest
  exact ⟨MvQPF.Fix.dest_mk, MvQPF.Fix.mk_dest⟩

theorem MvQPF.Fix.rec_inj {F} [MvFunctor F] [MvQPF F] {g : F (α ::: β) → β} (fInj : Function.Injective g) : Function.Injective $ MvQPF.Fix.rec (F := F) (α := α) g := by
  intro a b h
  apply MvQPF.Fix.ind_rec at h

/- open TypeVec -/
/- theorem TypeVec.map_inj {F} [MvFunctor F] [LawfulMvFunctor F] -/
/-     {f : Arrow α β} -/
/-     (h : ∀ i, Function.Injective (f i)) -/
/-     -- (h : Function.Injective f)  -/
/-     : -/
/-     Function.Injective (MvFunctor.map (F:=F) f) := by -/
/-   intro a b heq -/

  
/- theorem bij_symm {f : α → β} [Nonempty α] (bij : Function.Bijective f) : Function.Bijective (Function.invFun f) := by -/
/-   apply Function.bijective_iff_has_inverse.mpr -/
/-   use f -/
/-   constructor -/
/-   · simp [] -/
/-   · simp -/
open Function.Bijective in
theorem unfold_inj' {F} [instF : MvFunctor F] [instQ : MvQPF F] {α : TypeVec n} : Function.Bijective $ MvQPF.Fix.dest (F := F) (α := α) := by
  apply Function.bijective_iff_has_inverse.mpr
  use MvQPF.Fix.mk
  exact ⟨MvQPF.Fix.mk_dest, MvQPF.Fix.dest_mk⟩

  /- exact Function.Bijective.injective $ MvQPF.Fix.mk_dest_bij.symm -/

theorem unfold_inj {F} [instF : MvFunctor F] [instQ : MvQPF F] {α : TypeVec n} {a b : MvQPF.Fix F α} :
  (MvQPF.Fix.dest a) = (MvQPF.Fix.dest b) → a = b := by
  simp [MvQPF.Fix.dest, MvFunctor.map, MvPFunctor.map_eq]
  intro h
  induction a using MvQPF.Fix.ind generalizing b
  next a ih =>

  cases b using MvQPF.Fix.ind
  next b bih =>
  clear bih

  rcases ih with ⟨u, rfl⟩ 
  suffices (MvFunctor.map (fun _ => Subtype.val) u) = b by
    rw [this]
  
  simp_all

  simp only [MvQPF.Fix.rec_eq] at h
  repeat rw [← LawfulMvFunctor.comp_map] at h
  simp only [TypeVec.comp_id_append1] at h

  simp only [MvQPF.comp_map] at h

  have inj {a b : F (α ::: MvQPF.Fix F α)} :
      Function.Injective
        $ MvFunctor.map (F := F)
        (@TypeVec.id n α ::: MvQPF.Fix.mk ∘ MvQPF.Fix.rec (F:=F) (MvFunctor.map (@TypeVec.id n α ::: MvQPF.Fix.mk)))
      := by
    clear *-α F n
    refine MvFunctor.map_inj $ TypeVec.append1_injective ?_
    intro a b h
    suffices z : Function.Injective (MvQPF.Fix.mk ∘ MvQPF.Fix.rec (MvFunctor.map (@TypeVec.id n α ::: MvQPF.Fix.mk (F := F)))) by exact z h
    intro a b h
    apply Function.Bijective.injective MvQPF.Fix.mk_dest_bij at h
    apply MvQPF.Fix.rec_inj at h
    · trivial
    apply MvFunctor.map_inj
    apply TypeVec.append1_injective
    exact Function.Bijective.injective MvQPF.Fix.mk_dest_bij

    /- simp at h -/
    /- apply MvQPF.Fix.rec_unique at h -/
    /- refine MvPFunctor.map_inj ?a -/
  /- have inj {a b : F (α ::: MvQPF.Fix F α)} :  -/
  /-     MvFunctor.map (TypeVec.id ::: MvQPF.Fix.mk ∘ MvQPF.Fix.rec (MvFunctor.map (TypeVec.id ::: MvQPF.Fix.mk))) a -/
  /-     = MvFunctor.map (TypeVec.id ::: MvQPF.Fix.mk ∘ MvQPF.Fix.rec (MvFunctor.map (TypeVec.id ::: MvQPF.Fix.mk))) b -/
  /-     → a = b := by  -/
  /-   refine MvPFunctor.map_inj ?a -/
  apply inj
  · exact b
  · exact b
  · exact h

theorem QLs.cons.inj (h : QLs.cons ahd atl = QLs.cons bhd btl) : (ahd = bhd) ∧ (atl = btl) := by
  unfold cons at h
  apply Function.Bijective.injective MvQPF.Fix.mk_dest_bij at h
  injection h with eq₁ eq₂

  exact ⟨eq₁, eq₂⟩

theorem QLs.cons.injEq : (QLs.cons head tail = QLs.cons head tail) = (head = head ∧ tail = tail) := by
  apply propext
  constructor
  · exact QLs.cons.inj
  · rintro ⟨hdEq, tlEq⟩
    rw [hdEq, tlEq]


example { a b : QLs ℕ } (ha : a = QLs.nil) (hb : b = QLs.cons 0 .nil) (h : a = b) : False := by
  rw [ha, hb] at h

  exact QLs.noConfusion h

example { a b : QLs ℕ } (ha : a = .cons 0 .nil) (hb : b = .cons 1 .nil) (h : a = b) : ¬False := by
  rw [ha, hb] at h

  exact QLs.noConfusion h

/- def QLs.noConfusion (a b : QLs α) : Prop := -/
/-   a.casesOn' -/
/-     (b.casesOn' -/
/-       True -/
/-       fun _ _ => False) -/
/-     (fun _ _ => b.casesOn' -/
/-       False -/
/-       fun _ _ => True) -/

def QLs.casesOn
    {α : Type _}
    {motive : QLs α → Sort _}
    (t : QLs α)
    (nil : motive .nil)
    (cons : (head : α) → (tail : QLs α) → motive (.cons head tail))
    : motive t := by
  let t' := t
  let d : QLs.Shape α (QLs α) := MvQPF.Fix.dest t

  match h : d with
  | .nil       =>
    cases t
    · simp [MvQPF.Fix.dest_mk] at d
      sorry
    · sorry

  | .cons h tl => sorry
  
  /- let dest : QLs.Shape α (QLs α) := MvQPF.Fix.dest t -/

  /- match dest with -/
  /- | .nil => -/
  /-   have : t = .nil := by -/
  /-     induction t generalizing motive -/
  /-     case cons hd tl ih => -/
  /-       simp [QLs.Shape] at dest -/
  /-       sorry -/
  /-     · trivial -/
  /-   cast (by rw [this]) nil -/
  /- | .cons (a : α) (tl : QLs α) =>  -/
  /-   have : t = .cons a tl := sorry -/
  /-   cast (by rw [this]) $ cons a tl -/

def QLs.rec'
    {α : Type _}
    {motive : QLs α → Type _}
    (nil : motive .nil)
    (cons : (head : α) → (tail : QLs α) → motive tail → motive (.cons head tail))
    (t : QLs α) : motive t :=
  MvQPF.Fix.drec (match · with
    | .nil => nil
    | .cons (hd : α) (⟨tl, h_tl⟩ : Sigma motive) => by
        clear *-cons
        change motive (.cons hd tl)

        exact cons hd tl h_tl
  ) t

--TODO(@William): Fix.drec should have *two* universe, one for `F` and 
--                an independent universe for the motive `β`
--                Also PSigma

@[elab_as_elim, eliminator]
def QLs.ind' {motive : QLs α → Prop}
    (nil : motive (.nil))
    (cons : (hd : α) → (tl : QLs α) → motive tl → motive (.cons hd tl))
    : (ls : QLs α) → motive ls :=
  MvQPF.Fix.ind
    (p := motive)
    (match ·, · with
    | .cons (hd : α) (tl : QLs α), ih => 
        have ih : motive tl := by
          simp only [MvFunctor.LiftP, TypeVec.PredLast, Fin2.instOfNatFin2HAddNatInstHAddInstAddNatOfNat] at ih
          clear *-ih
          rcases ih with ⟨witness, proof⟩
          change QLs.Shape { _hd : α // True } { ls // motive ls} at witness

          cases witness
          case intro.nil => contradiction
          case intro.cons hd' tl' =>
            rcases hd' with ⟨hd', _⟩
            rcases tl' with ⟨tl', ih_tl⟩

            change Shape.cons hd' tl' = _ at proof
            injection proof with eq₁ eq₂

            subst eq₁ eq₂

            exact ih_tl

        (cons hd tl ih)
    | .nil, _ => nil)

/- instance [SizeOf α]: SizeOf (QLs α) where -/
/-   sizeOf := MvQPF.Fix.rec fun x => match x with -/
/-     | .nil => 0 -/
/-     | .cons x y => SizeOf.sizeOf x + y.succ -/

instance : SizeOf (QLs α) where
  sizeOf := MvQPF.Fix.rec (match · with
    | .nil => 0
    | .cons _ y => y.succ)

@[simp]
theorem sizeOf_cons : sizeOf (QLs.cons a x) = sizeOf x + 1 := by
  simp [sizeOf, QLs.cons, MvQPF.Fix.rec_eq]
  rfl

inductive Tree α
  | br (x : α) (l : Tree α) (r : Tree α)
  | lf (x : α)

data Qt α
  | br (x : α) (l : Qt α) (r : Qt α)
  | ss (x : α) (d : Qt α)
  | lf (x : List α)

/- open MvFunctor in -/
def Qt.rec'
    {α : Type}
    {motive : Qt α → Type}
    (br : (x : α) → (l : Qt α) → (r : Qt α) → motive l → motive r → motive (.br x l r))
    (ss : (x : α) → (d : Qt α) → motive d → motive (.ss x d))
    (lf : (x : List α) → motive (.lf x))
    : (t : Qt α) → motive t :=
  MvQPF.Fix.drec (match · with
    | .br _ ⟨_, h_l⟩ ⟨_, h_r⟩ =>
      br _ _ _ h_l h_r

    | .ss _ ⟨_, h_d⟩ =>
      ss _ _ h_d

    | .lf _ =>
      lf _
    )

#print axioms Qt.rec

/- instance : SizeOf (Qt α) where -/
/-   sizeOf := MvQPF.Fix.rec (β := Nat) (match · with -/
/-     | .lf _ => 0 -/
/-     | .br _ l r => l.succ + r.succ - 1) -/

/- theorem size_growth (v : α) (l : Qt α) (r : Qt α) : sizeOf (Qt.br v l r) = 1 + sizeOf l + sizeOf r := by -/
/-   simp [sizeOf, Qt.br, MvQPF.Fix.rec_eq] -/
/-   sorry -/

--TODO: rec_eq ought to be simp
#check MvQPF.Fix.rec_eq

-- TODO(@William): read up on show

/- theorem lt_cons (x : QLs α): sizeOf x < sizeOf (QLs.cons a x) := by -/
/-   induction x -/
/-   · reduce -/
/-     exact Nat.le_refl 1 -/
/-   case f hd tl ih => -/

/-     sorry -/

  /- simp -/



def map' (f : α → β) : QLs α → QLs β :=
  Prod.fst ∘ MvQPF.Fix.rec (match · with
    | .cons hd ⟨tl, im⟩ => ⟨.cons (f hd) tl, .cons tl im⟩
    | .nil => ⟨.nil, QLs.nil⟩)

/- def ack (a : QLs Unit) (b : QLs Unit): QLs Unit := -/
/-   a.rec fun a => match a with -/
/-     | .nil => .cons () b -/
/-     | .cons Unit n => .cons -/

/- set_option pp.explicit true in -/
-- set_option pp.instances true in
open Vec in

def map (f : α → β) (ls : QLs α) : QLs β :=
  let x := MvQPF.Fix.dest ls

  match hx : x with
  | .nil => .nil
  | .cons hd tl =>
    .cons (f hd) (map f tl)
termination_by sizeOf ls
decreasing_by
  simp_wf
  change QLs α at tl
  change α at hd
  simp [x] at hx
  clear x
  obtain rfl : ls = .cons hd tl := by
    cases ls
    case nil => contradiction

    case cons _ tl' _ =>
      simp [QLs.cons, MvQPF.Fix.dest_mk] at hx
      injection hx with hdeq tleq
      rw [hdeq, tleq]
  simp

inductive RoseTree (α : Type) 
  | node : α → List (RoseTree α) → RoseTree α

data QRose α
  | node : α → List (QRose α) → QRose α

def QRose.ind
  {motive_tree : QRose α → Prop}
  {motive_list : List (QRose α) → Prop}
  (node : (a : α) → (a_1 : List (QRose α)) → motive_list a_1 → motive_tree (QRose.node a a_1))
  (nil : motive_list [])
  (cons : (head : QRose α) → (tail : List (QRose α)) → motive_tree head → motive_list tail → motive_list (head :: tail)):
  (tree : QRose α) → motive_tree tree :=
  MvQPF.Fix.ind
    (p := motive_tree)
    (match ·, · with
    | .node (hd : α) (ls : List $ QRose α), ih => 
      have ih_ls: motive_list ls := by
        simp [MvFunctor.LiftP, TypeVec.PredLast] at ih
        clear *-ih cons nil
        rcases ih with ⟨witness, proof⟩
        change Shape
          { _hd : α // True } { _ls : _ // motive_tree _ls }
          (List { subtree : _ // motive_tree subtree }) at witness

        cases witness
        case intro.node hd' ls' =>
          rcases hd' with ⟨hd', _⟩

          change Shape.node hd' _ = _ at proof
          simp only [
            Fin2.instOfNatFin2HAddNatInstHAddInstAddNatOfNat,
            TypeVec.comp,
            Shape.node.injEq
          ] at proof

          rcases proof with ⟨rfl, eq₂⟩

          induction ls generalizing ls'
          case nil => exact nil
          case cons hd tl ih =>
            cases ls'
            case nil =>
              exact List.noConfusion eq₂
              /- exact ((fun bbid => bbid) (by contradiction)) -/
            case cons hd' tl' =>
              injection eq₂ with hd_eq tl_eq
              /- change hd' = hd at hd_eq -/
              subst hd_eq

              apply cons hd' tl
              · exact hd'.property
              · exact ih tl' tl_eq

      node hd ls ih_ls
    )

inductive MyLs (α : Type _)
  | nil
  | cons (hd : α) (tl : MyLs α)

codata QCoTree α
  | br : α → QCoTree α → QCoTree α → QCoTree α

def QCoTree.corec (f : β → QCoTree.Base α β) (b : β) : QCoTree α :=
  MvQPF.Cofix.corec f b

codata QCoRoseTree α
  | br : α → QLs (QCoTree α) → QCoRoseTree α

def QCoRoseTree.corec (f : β → QCoRoseTree.Base α β) (b : β) : QCoRoseTree α :=
  MvQPF.Cofix.corec f b

def QLs.noConfusionType' (P : Prop) (a b : QLs α) : Prop :=
  QLs.casesType
    (fun hd1 tl1 =>
      QLs.casesType (fun hd2 tl2 => (hd1 = hd2 → tl1 = tl2 → P) → P) P b)
    (QLs.casesType (fun _ _ => P) (P → P) b)
    a

#print List.noConfusion
#print List.noConfusionType

/- def QLs.noConfusion' {v1 v2 : QLs α} (h12 : v1 = v2) : QLs.noConfusionType' P a b := -/
/-   Eq.ndrec (motive := fun a => v1 = a → QLs.noConfusionType' P v1 a) -/
/-     (fun h11 => QLs.cases (fun head tail a => sorry) (fun a => a) v1) h12 h12 -/
  

/- def QLs.cases'  -/

theorem TypeVec.idx {α : TypeVec n} : (TypeVec.append1 α b) (Fin2.fs k) = α k := by simp [TypeVec.append1]
theorem TypeVec.id_idx : @TypeVec.id n α k b = b := by simp [TypeVec.id]

#print QLs.Shape.noConfusionType
def QLs.noConfusion₂ {v1 v2 : QLs α} (h12 : v1 = v2) : QLs.noConfusionType' P v1 v2 := by
/- def QLs.noConfusion₂ {v1 v2 : QLs α} (h12 : v1 = v2) : QLs.Shape.noConfusionType P v1 v2 := by -/
  cases v1
  <;> cases v2
  <;> dsimp [nil, cons] at h12
  <;> apply Function.Bijective.injective MvQPF.Fix.mk_dest_bij at h12
  <;> have := @QLs.Shape.noConfusion _ _ P _ _ h12
  · intro p
    exact p
  · exact this
  · exact this
  · intro p
    simp [TypeVec.comp] at p
    simp [
      TypeVec.append1,
      TypeVec.id,
      TypeVec.Arrow,
      TypeVec.id,
      TypeVec.idx,
      TypeVec.id_idx,
      TypeVec.dropFun,
      TypeVec.lastFun,
      TypeVec.splitFun] at p
    unfold TypeVec.id TypeVec.append1 at p

    change (_ → P) at p
    simp [Shape.noConfusionType] at this
    sorry

/- #exit -/

def QLs.noConfusion' {v1 v2 : QLs α} (h12 : v1 = v2) : QLs.noConfusionType' P v1 v2 :=
  @Eq.ndrec _ v1
    (fun a => v1 = a → QLs.noConfusionType' P v1 a)
    (fun _ =>
      @QLs.ind
        α
        (fun { v1 } => QLs.noConfusionType' P v1 v1)
        (fun hd tl x p => by
          simp [TypeVec.comp] at p
          simp [
            TypeVec.append1,
            TypeVec.id,
            TypeVec.Arrow,
            TypeVec.id,
            TypeVec.idx,
            TypeVec.id_idx,
            TypeVec.dropFun,
            TypeVec.lastFun,
            TypeVec.splitFun] at p
          unfold TypeVec.id TypeVec.append1 at p
          apply p
          change (_ : QLs α) = (_ : QLs α)
          sorry
        )
        id
        v1)
    _ h12 h12

/- #exit -/

def List.noConfusionX
   {v1 v2 : List α} (h12 : v1 = v2) : List.noConfusionType P v1 v2 :=
  @Eq.ndrec _ v1
    (fun a => v1 = a → List.noConfusionType P v1 a)
    (fun _ => List.casesOn (motive := fun { v1 } => List.noConfusionType P v1 v1) v1 id fun head tail a => a (Eq.refl head) (Eq.refl tail))
    /- (fun _ => @List.casesOn α (fun {v1} => @List.noConfusionType α P v1 v1) v1 id fun head tail a => a (Eq.refl head) (Eq.refl tail)) -/
    _ h12 h12

#print QLs.noConfusion


#print List.noConfusion
#print MyLs.noConfusionType
/- #print QLs.noConfusionType -/
#print QRose.ind

/- theorem QRose.extracted_1 {α : Type} {motive_tree : QRose α → Prop} {motive_list : List (QRose α) → Prop} -/
/-   (nil : motive_list []) -/
/-   (cons : ∀ (head : QRose α) (tail : List (QRose α)), motive_tree head → motive_list tail → motive_list (head :: tail)) -/
/-   (hd : QRose α) (tl : List (QRose α)) -/
/-   (ih : -/
/-     ∀ (ls' : List { subtree // motive_tree subtree }), MvFunctor.map (fun i => Subtype.val) ls' = tl → motive_list tl) -/
/-   (eq₂ : MvFunctor.map (fun i => Subtype.val) List.nil = hd :: tl) : motive_list (hd :: tl) := sorry -/

/- theorem x : List.map f (hd' :: tl') = hd :: tl → f hd' = hd ∧ List.map f tl' = tl := by -/
/-   intro a -/
/-   injection a with c d -/

/-   exact ⟨c, d⟩ -/

/- #print x -/

open MvFunctor in
/- example {f : α → β} : (fun i => f) <$$> (@QLs.nil α) = (@QLs.nil β) := sorry -/
example {f : α → β} : MvFunctor.map (F := QLs.Uncurried) (fun i => id) a = a := by
  simp [MvFunctor.map]
  

example {f : α → β} : MvFunctor.map (F := QLs.Uncurried) (fun i => f) (QLs.cons hd' tl')
  = QLs.cons (Subtype.val hd') (MvFunctor.map (fun _ => Subtype.val) tl') := sorry

data QRose' α
  | node : α → QLs (QRose' α) → QRose' α

def QRose'.ind
  {motive_tree : QRose' α → Prop}
  {motive_list : QLs (QRose' α) → Prop}
  (node : (a : α) → (a_1 : QLs (QRose' α)) → motive_list a_1 → motive_tree (QRose'.node a a_1))
  (nil : motive_list QLs.nil)
  (cons : (head : QRose' α) → (tail : QLs (QRose' α)) → motive_tree head → motive_list tail → motive_list (.cons head tail)):
  (tree : QRose' α) → motive_tree tree :=
  MvQPF.Fix.ind
    (p := motive_tree)
    (match ·, · with
    | .node (hd : α) (ls : QLs $ QRose' α), ih => 
      have ih_ls: motive_list ls := by
        simp [MvFunctor.LiftP, TypeVec.PredLast] at ih
        clear *-ih cons nil
        rcases ih with ⟨witness, proof⟩
        change Shape
          { _hd : α // True } { _ls : _ // motive_tree _ls }
          (QLs { subtree : _ // motive_tree subtree }) at witness

        cases witness
        case intro.node hd' ls' =>
          rcases hd' with ⟨hd', _⟩

          change Shape.node hd' _ = _ at proof
          simp only [
            Fin2.instOfNatFin2HAddNatInstHAddInstAddNatOfNat,
            TypeVec.comp,
            Shape.node.injEq
          ] at proof

          rcases proof with ⟨rfl, eq₂⟩

          induction ls generalizing ls'
          case nil => exact nil
          case cons hd tl ih =>
            cases ls'
            case nil x =>
              /- exfalso -/
              exact QLs.noConfusion eq₂
              /- trivial -/
              /- exact QLs.noConfusion eq₂ -/
              /- exac -/
            case cons hd' tl' ih' =>
              simp at eq₂
              change QLs.cons hd'.val (MvFunctor.map (F := QLs.Uncurried) (fun _ => Subtype.val) (tl' : QLs.Uncurried (fun i => Subtype motive_tree ))) = _ at eq₂
              sorry
              /- injection eq₂ with -/
              /- injection eq₂ with hd_eq tl_eq -/
              /- have ⟨hd_eq, tl_eq⟩ := QLs.cons_injection eq₂ -/
              /- /- change hd' = hd at hd_eq -/ -/
              /- subst hd_eq -/

              /- apply cons hd' tl -/
              /- · exact hd'.property -/
              /- · exact ih tl' tl_eq -/

      node hd ls ih_ls
    )


data ProdLs α
  | cons : α × ProdLs α → ProdLs α
  | lf

@[elab_as_elim, eliminator]
def ProdLs.ind
    {motive : ProdLs α → Prop}
    {motive_prod : α × ProdLs α → Prop}
    (lf : motive (.lf))
    (cons : (hd : α × ProdLs α) → motive_prod hd → motive (.cons hd))
    (prod : (lhs : α) → (rhs : ProdLs α) → motive rhs → motive_prod ⟨lhs, rhs⟩)

    : (ls : ProdLs α) → motive ls :=
  MvQPF.Fix.ind
    (p := motive)
    (match ·, · with
    | .cons (hd : α × ProdLs α), ih => 
        have ih : motive_prod hd := by
          simp only [MvFunctor.LiftP, TypeVec.PredLast, Fin2.instOfNatFin2HAddNatInstHAddInstAddNatOfNat] at ih
          clear *-ih
          rcases ih with ⟨witness, proof⟩
          /- change Shape { _hd : α // True } { ls // motive ls} at witness -/
          change Shape { _a : _ // True } { _b : _ // _ } ({ _c : _ // True } × { _d : _ // _ }) at witness

          sorry
        cons hd ih
    | .lf => lf)
          /- cases witness -/

/- decreasing_by { -/

/-   simp [*] -/
/-   dsimp only [InvImage, WellFoundedRelation.rel] -/
/-   unfold WellFoundedRelation.rel Nat.lt_wfRel -/
/-   simp -/

/-   exact this -/ /- } -/


example: Acc (fun (a b : Nat) => a < b) 1 := by
  constructor
  intro x hx
  constructor
  apply Nat.lt_one_iff.mp at hx
  intro y hy
  rw [hx] at hy
  contradiction

/- #check measure id -/
/- #print prefix WellFoundedRelation -/
/- #check WellFounded.fix -/

#print WellFounded.fix

example: Acc (fun (a b : Nat) => a < b) 2 := by
  constructor
  intro x hx
  constructor
  apply Nat.le_of_lt_succ at hx
  intro y hy
  have hy := Nat.lt_of_lt_of_le hy hx |> Nat.le_of_lt_succ |> Nat.le_zero.mp
  constructor
  intro z hz
  rw [hy] at hz
  contradiction

-- Can be generalised to any WellFoundedRelation
/- theorem strong_induction_nat (P: ℕ → Prop) : P 0 ∧ (∀x, (∀y < x, P y) → P x) → ∀ n, P n := by -/
/-   intro ⟨base, step⟩ -/

/-   intro n -/

/-   induction n -/
/-   · exact base -/
/-   case succ x holds_for_x => { -/
/-     apply step -/

/-     intro y hy -/

/-     induction y -/
/-     · exact base -/
/-     case a.succ x' holds_for_x' => { -/
/-       apply Nat.succ_lt_succ_iff.mp at hy -/

/-     } -/
/-   } -/

example n : Acc Nat.lt n := by
  apply strong_induction_nat
  constructor
  · constructor
    intro _ x
    contradiction
  · intro x y hxy h
    constructor
    intro z hz

  /- induction n -/
  /- · constructor -/
  /-   intro _ x -/
  /-   contradiction -/
  /- case succ x hx => { -/
  /-   constructor -/
  /-   intro y hy -/
  /-   apply Nat.le_of_lt_succ at hy -/

  /-   sorry -/
  /- } -/

theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => Nat.sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (div_lemma h) y + 1
  else 0

noncomputable def div := WellFounded.fix (measure id).wf div.F

/- example n: Acc (fun (a b : Nat) => a < b) n := by -/
/-   induction n <;> (constructor; intro x hx) -/
/-   · contradiction -/
/-   · induction x -/
/-     · constructor -/
/-       intro _ cont -/
/-       contradiction -/

