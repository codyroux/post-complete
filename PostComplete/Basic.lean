import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finite.Basic
import Mathlib.Data.FinEnum

#check ![true, true, false, true]

abbrev Func n := (Fin n → Bool) → Bool

#print Fin

def unit {α} : Fin 0 → α := λ h ↦ by cases h; omega

#print List.ofFn


@[simp]
lemma unitUnique (x : Fin 0 → Bool) : x = unit := by
  exact List.ofFn_inj.mp rfl

#print unit

#check λ f : Func 2 ↦ f ![true, true]

#check ![]

#print Func

#print Set

def Family := ∀ n : ℕ, Set (Func n)

-- A tree of composition of n inputs, or "vars"
-- Where each node is a symbolic application of
-- f ∈ F
inductive AppTree (F : Family) n :=
| Var : Fin n → AppTree F n
| App : ∀ {m} f, f ∈ F m → (Fin m → AppTree F n) → AppTree F n

-- Hey we can eval these!
def evalTree (t : AppTree F n) : Func n :=
  λ i ↦
  match t with
  | .Var n => i n
  | .App f _ t => f (λ m ↦ evalTree (t m) i)

#print FinEnum

instance bFinEnum : FinEnum Bool :=
⟨  2, ⟨ λ b ↦ if b then 1 else 0,
       λ i ↦ if i.val = 0 then false else true,
  by
    simp [Function.LeftInverse]
  ,
  by
    simp [Function.RightInverse, Function.LeftInverse]
    intros x; split
    case isTrue h => omega
    case isFalse h => omega
⟩
⟩

instance finEnumFunc n : FinEnum (Func n) := inferInstance

def FuncList (n : ℕ) : List (Func n) :=
  @FinEnum.toList _ (finEnumFunc n)

@[simp]
lemma mem_FuncList n : ∀ f, f ∈ FuncList n := by
  intros f; apply FinEnum.mem_toList

lemma func_to_finite n (P : Func n → Prop) :
  (∀ f ∈ FuncList n, P f) → ∀ f, P f := by
  intros p_bound f; apply p_bound; simp

#print FinEnum.toList

#reduce List.length (finEnumFunc 2).toList

-- Are functions extensional?
lemma test : (λ b ↦ if b then false else true) = not :=
by
  apply funext; intro b; split <;> simp at * <;> assumption

class HasEval (F : Family) (n : ℕ) (f : Func n) : Type where
  tree : AppTree F n
  is_evaltree : evalTree tree = f

-- FIXME: should this be a sigma?
def CompleteForFN (F G : Family) (n : ℕ) : Prop := ∀ (f : Func n), f ∈ G n → (Nonempty $ HasEval F n f)

def Full : Family := λ _ ↦ Set.univ

def CompleteForN (F : Family) : ℕ → Prop := CompleteForFN F Full

-- Shockingly, this definition does not allow us to do any of the "usual" proofs!
def Complete F := ∀ n, CompleteForN F n

def QuasiComplete F := ∀ n, n > 0 → CompleteForN F n

def id1 : Func 1 := λ b ↦ b 0

def not1 : Func 1 := λ b ↦ ! (b 0)

def true_n : Func n := λ _ ↦ true

def false_n : Func n := λ _ ↦ false

def or2 : Func 2 := λ b ↦ (b 0) || (b 1)

def and2 : Func 2 := λ b ↦ (b 0) && (b 1)

#print Set

@[simp]
def NAOT : ∀ n, Set (Func n)
| 0 => { f | f = true_n }
| 1 => { f | f = not1 }
| 2 => {f | f = and2 ∨ f = or2 }
| _ => ∅

def NAOT.true : {f | f ∈ NAOT 0} := ⟨ true_n, by simp ⟩
def NAOT.not : {f | f ∈ NAOT 1} := ⟨ not1, by simp ⟩
def NAOT.and : {f | f ∈ NAOT 2} := ⟨ and2, by simp ⟩
def NAOT.or : {f | f ∈ NAOT 2} := ⟨ or2, by simp ⟩

def inst_arg (i : Fin n → Bool)(k : ℕ)(_ : k < n + 1)(b : Bool) : Fin (n+1) → Bool
| ⟨ l, _⟩ =>
  if h: l < k then i ⟨ l, by omega⟩
  else if h': l = k then b
  else i ⟨ l - 1, by omega⟩

def inst_fun (f : Func (n+1)) (k : ℕ) (h : k < n + 1) (b : Bool) : Func n :=
  λ arg ↦ f (inst_arg arg k h b)

#print Func

instance subsetFam : HasSubset Family :=
 ⟨λ F F' ↦ ∀ n, F n ⊆ F' n⟩

def bumpTree {F F'} (sub : F ⊆ F') (t : AppTree F n) : AppTree F' n :=
match t with
| .Var n => .Var n
| .App f _ ts => .App f (by apply sub; trivial) (λ b ↦ bumpTree sub (ts b))

lemma eval_bumpTree_eq  {F F'} (sub : F ⊆ F') (t : AppTree F n) :
  evalTree t = evalTree (bumpTree sub t) :=
by
  cases t
  case Var n => simp [bumpTree, evalTree]
  case App =>
    simp [bumpTree, evalTree]
    apply funext
    intros b
    apply congrArg
    apply funext
    intros i;
    apply congr_fun
    apply eval_bumpTree_eq

def var_n : Fin n → AppTree F n := λ i ↦ .Var i

def f_tree (f : Func n) (f_mem : f ∈ F n) : AppTree F n := .App f f_mem var_n

@[simp]
lemma eval_app_eq {F : Family} (f : Func n) (h : f ∈ F n) :
  evalTree (f_tree f h) = f := by
simp [evalTree]

#print HasEval

lemma complete_for_n_mon_1 (F F') n : F ⊆ F' → CompleteForN F n → CompleteForN F' n :=
by
  simp [CompleteForN, CompleteForFN]
  intros sub h f _
  specialize h f _; trivial
  cases h
  case intro _ t =>
    exists (bumpTree sub t.tree)
    rw [← eval_bumpTree_eq]; simp [t.is_evaltree]

#check List.indexOf_get


instance inhabitedAppTree {n : ℕ} [NeZero n] : Inhabited (AppTree F n) :=
⟨ .Var 0 ⟩

lemma list_complete {F} [NeZero n] (ts : List (AppTree F n)) :
  let fs := FuncList n
  ts.length = fs.length →
  (∀ (i : ℕ) (h : i < fs.length),
  evalTree (ts.get! i) = fs.get ⟨i, h⟩ ) →
  CompleteForN F n
:= by
intros fs _ tree_mem f _
have f_mem_funclist : f ∈ fs :=
  by apply mem_FuncList
let i := List.indexOf f fs
use (ts.get! i)
have i_lt_len : i < fs.length := by
  exact List.indexOf_lt_length.mpr f_mem_funclist
rw [← @List.indexOf_get _ _ f]
apply tree_mem
exact i_lt_len


#print Family

def EvalMap (F G : Family) : Type := Π {n} f, f ∈ F n → AppTree G n

def EvalMapSound {F G} (e : EvalMap F G) :=
  ∀ n f (h : f ∈ F n), evalTree (e f h) = f

-- This is just "plain" substitution for trees, which
-- takes a term over "n variables" to a term over "m variables"
def subst {F} (t : AppTree F n) (ts : Fin n → AppTree F m) : AppTree F m :=
match t with
| .Var k => ts k
| .App f mem us =>
  .App f mem (λ i ↦ subst (us i) ts)

#print AppTree

def mapSubst {F G} (e : EvalMap F G) (t : AppTree F n) : AppTree G n :=
match t with
| .Var k => .Var k
| .App f mem ts =>
    subst (e f mem) (λ i ↦ mapSubst e (ts i))

#print EvalMapSound

@[simp]
def comp (f : Func n) (g : Fin n → Func m) : Func m :=
  λ b ↦ f (λ i ↦ g i b)

lemma eval_subst (t : AppTree F n) (s : Fin n → AppTree F m) :
   evalTree (subst t s) = comp (evalTree t) (λ i ↦ evalTree (s i)) := by
cases t
case Var =>
  simp [subst, comp, evalTree]
  -- eta all over the place
  apply Eq.refl
case App m f f_mem ts =>
  simp [subst, comp, evalTree]
  apply funext; intros bs
  simp [comp]
  apply congrArg
  apply funext; intros i
  rw [eval_subst]
  apply Eq.refl

#print EvalMapSound

@[simp]
lemma mapSubst_sound {F G} (e : EvalMap F G) : EvalMapSound e →
  ∀ (t : AppTree F n), evalTree (mapSubst e t) = evalTree t
:= by
  intros sound t
  cases t
  case Var i => simp [mapSubst]; trivial
  case App n f f_mem ts =>
  simp [mapSubst, subst]
  rw [eval_subst]
  rw [sound]
  apply funext; intros bs; simp [evalTree]
  apply congrArg; apply funext; intro i
  rw [mapSubst_sound]
  trivial

lemma eval_mon_complete {F F'} : CompleteForN F' n →
  CompleteForFN F F' n →
  CompleteForN F n
:= by sorry

#print AppTree.App

#print HasEval

instance hasEvalF F n f (h : f ∈ F n) : HasEval F n f :=
by
  use (.App f h (λ i ↦ .Var i))
  simp [evalTree]


instance hasEvalApp0 F f (h : f ∈ F 0) : HasEval F 0 f :=
by
  use (.App f h unit)
  simp [evalTree]
  apply funext; simp

instance hasEvalApp1 F n f (h : f ∈ F 1) (g : Func n) [g_eval : HasEval F n g] : HasEval F n (λ b ↦ f ![g b]) :=
by
  use (.App f h ![g_eval.tree])
  simp [evalTree]
  apply funext; intros b
  rw [g_eval.is_evaltree]
  congr
  apply funext; simp


instance hasEvalApp2 F n f (h : f ∈ F 2) (g₁ g₂ : Func n) [g₁_eval : HasEval F n g₁] [g₂_eval : HasEval F n g₂] : HasEval F n (λ b ↦ f ![g₁ b, g₂ b]) :=
by
  use (.App f h ![g₁_eval.tree, g₂_eval.tree])
  simp [evalTree]
  apply funext; intros b
  congr; apply funext; intros i
  match i with
  | 0 => simp; rw [g₁_eval.is_evaltree]
  | 1 => simp; rw [g₂_eval.is_evaltree]


lemma complete_NAOT_0 : CompleteForN NAOT 0 := by
  simp [CompleteForN, CompleteForFN, Full, Func]
  intros f
  cases h : (f unit)
  case false =>
    have h' : f = λ b ↦ not1 ![true_n b] :=
    by
      apply funext
      intros x; simp [h, not1, true_n]
    rw [h']
    have has_eval_true : HasEval NAOT 0 true_n :=
      by apply hasEvalF; simp
    constructor; apply hasEvalApp1; simp
  case true =>
    constructor
    apply hasEvalF; simp
    apply funext; simp [true_n]; trivial

#check subst

def liftAppTree (t : AppTree F n) : AppTree F (n+1) :=
  subst t (λ i ↦ .Var i)

#check HasEval
#print inst_fun

instance hasEvalInst [HasEval F (n+1) f] [HasEval F 0 true_n] [HasEval F 0 false_n] : HasEval F n (inst_fun f n k b) :=
by sorry

theorem complete_NAOT : Complete NAOT :=
by
  intros n
  cases n
  case zero => apply complete_NAOT_0
  case succ n =>
    intros f h
    let f_true : Func n := inst_fun f n (by simp) true
    let f_false : Func n := inst_fun f n (by simp) false
    let ⟨ tree_f_true ⟩ := complete_NAOT _ f_true (by simp [Full])
    let ⟨ tree_f_false ⟩ := complete_NAOT _ f_false (by simp [Full])
    constructor
    -- cases tree_f_true
    -- cases tree_f_false
    -- case intro.intro t_true h₁ t_false h₂ =>
    --   exists (orSyn (andSyn (.Var n) (liftAppTree t_true))
    --          (andSyn (notSyn (.Var n)) (liftAppTree t_false)))
    sorry
