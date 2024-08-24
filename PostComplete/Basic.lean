import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finite.Basic
import Mathlib.Data.FinEnum

#check ![true, true, false, true]

abbrev Func n := (Fin n → Bool) → Bool

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

-- FIXME: should this be a sigma?
def CompleteForFN (F G : Family) (n : ℕ) : Prop := ∀ (f : Func n), f ∈ G n → ∃ (t : AppTree F n) , evalTree t = f

def Full : Family := λ _ ↦ Set.univ

def CompleteForN (F : Family) : ℕ → Prop := CompleteForFN F Full

-- Shockingly, this definition does not allow us to do any of the "usual" proofs!
def Complete F := ∀ n, CompleteForN F n

def QuasiComplete F := ∀ n, n > 0 → CompleteForN F n

def not1 : Func 1 := λ b ↦ ! (b 0)

def true_n : Func n := λ _ ↦ true

def false_n : Func n := λ _ ↦ false

def or2 : Func 2 := λ b ↦ (b 0) || (b 1)

def and2 : Func 2 := λ b ↦ (b 0) && (b 1)

#print Set

@[simp]
def NotTrueFam : ∀ n, Set (Func n)
| 0 => ∅
| 1 => { f | f = not1 ∨ f = true_n }
| _ => ∅

@[simp]
def NotAndOrFam : ∀ n, Set (Func n)
| 0 => ∅
| 1 => { f | f = not1 }
| 2 => {f | f = and2 ∨ f = or2 }
| _ => ∅

#print NotAndOrFam

lemma test' : and2 ∈ NotAndOrFam 2 := by simp

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

@[simp]
lemma eval_app_eq {F : Family} (f : Func n) (h : f ∈ F n) :
  evalTree (.App f h var_n) = f := by
simp [evalTree]

lemma complete_for_n_mon_1 (F F') n : F ⊆ F' → CompleteForN F n → CompleteForN F' n :=
by
  simp [CompleteForN, CompleteForFN]
  intros sub h f _
  specialize h f _; trivial
  cases h
  case intro t eq_t =>
    exists (bumpTree sub t)
    rw [← eval_bumpTree_eq]; trivial


lemma list_complete {F} (ts : List (AppTree F n)) : False
/- (same_len : (FuncList n.length) = ts.length) →
   (∀ k : (Fin (FuncList n).length), evalTree (ts.get k) = (FuncList n).get k) →
  CompleteForN F n
 -/
 := by
  sorry

#print Family

def EvalMap (F G : Family) : Type := Π {n} f, f ∈ F n → AppTree G n

def EvalMapSound {F G} (e : EvalMap F G) :=
  ∀ n f (h : f ∈ F n), evalTree (e f (by trivial)) = f

def appTreeSubst {F} (t : AppTree F n) (ts : Fin n → AppTree F m) : AppTree F m :=
match t with
| .Var k => ts k
| .App f mem us =>
  .App f mem (λ i ↦ appTreeSubst (us i) ts)

#print AppTree

def mapSubst {F G} (e : EvalMap F G) (t : AppTree F n) : AppTree G n :=
match t with
| .Var k => .Var k
| .App f mem ts =>
    appTreeSubst (e f mem) (λ i ↦ mapSubst e (ts i))

@[simp]
def mapSubst_sound {F G} (e : EvalMap F G) : EvalMapSound e →
  ∀ (t : AppTree F n), evalTree (mapSubst e t) = evalTree t
:= by sorry

lemma eval_mon_complete {F F'} : CompleteForN F' n →
  (∀ f ∈ F' n, ∃ t : AppTree F n, evalTree t = f) →
  CompleteForN F n
:= by sorry

lemma complete_NotTrue_1 : CompleteForN NotTrueFam 1 := by
  intros f
  have h_case :
  (f ![true] = true ∧ f ![false] = true) ∨
  (f ![true] = false ∧ f ![false] = true) ∨
  (f ![true] = false ∧ f ![false] = false) ∨
  (f ![true] = true ∧ f ![false] = false) := by
    sorry
  cases h_case
  case inl h => sorry
  case inr h => sorry


theorem complete_NotAndOrFam : QuasiComplete NotAndOrFam :=
by
  intros n
  cases n
  case zero => intros _ h; omega
  case succ n =>
    intros _ f
    let f_true : Func n := inst_fun f n (by simp) true
    let f_false : Func n := inst_fun f n (by simp) false
    let tree_f := complete_NotAndOrFam _ _ f_true
    sorry
