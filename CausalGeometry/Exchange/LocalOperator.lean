import Mathlib.Tactic

/-!
# Local two-component operators, with explicit arity boundaries

The lists here are observation fibers, not replacement causal histories.
The total helper leaves an unavailable slot unchanged; braid relations are
proved ONLY when all three slots exist. The sized API enforces that boundary.
No inverse, involutivity or Yang--Baxter law is bundled into an arbitrary R.
-/
namespace CausalGeometry.Exchange.LocalOperator

universe u
variable {A : Type u}

abbrev PairOperator (A : Type u) := (A × A) → (A × A)
abbrev Sized (A : Type u) (n : Nat) := {xs : List A // xs.length = n}

/-- Apply an operator to two adjacent entries, keeping the other entries. -/
def stepList (R : PairOperator A) : Nat → List A → List A
  | 0, a :: b :: xs => (R (a, b)).1 :: (R (a, b)).2 :: xs
  | i + 1, a :: xs => a :: stepList R i xs
  | _, xs => xs

@[simp] theorem stepList_length (R : PairOperator A) (i : Nat) (xs : List A) :
    (stepList R i xs).length = xs.length := by
  induction i generalizing xs with
  | zero => cases xs with
    | nil => rfl
    | cons a xs => cases xs <;> rfl
  | succ i ih => cases xs <;> simp [stepList, ih]

/-- A left context shifts the actual location, not the operator itself. -/
theorem stepList_prefix (R : PairOperator A) (u xs : List A) (i : Nat) :
    stepList R (u.length + i) (u ++ xs) = u ++ stepList R i xs := by
  induction u with
  | nil => rfl
  | cons a u ih => simpa [stepList, Nat.succ_add] using congrArg (List.cons a) ih

/-- A right context is unaffected when both operated slots lie before it. -/
theorem stepList_suffix (R : PairOperator A) (i : Nat) (xs ys : List A)
    (h : i + 2 ≤ xs.length) :
    stepList R i (xs ++ ys) = stepList R i xs ++ ys := by
  induction i generalizing xs with
  | zero =>
      cases xs with
      | nil => simp at h
      | cons a xs => cases xs with
        | nil => simp at h
        | cons b xs => rfl
  | succ i ih =>
      cases xs with
      | nil => simp at h
      | cons a xs =>
          have ht : i + 2 ≤ xs.length := by simpa using h
          simpa [stepList] using congrArg (List.cons a) (ih xs ht)

/-- Disjoint local operators commute without any Yang--Baxter hypothesis. -/
theorem stepList_far (R : PairOperator A) (i j : Nat) (h : i + 1 < j)
    (xs : List A) :
    stepList R j (stepList R i xs) = stepList R i (stepList R j xs) := by
  induction i generalizing j xs with
  | zero =>
      cases j with
      | zero => omega
      | succ j => cases j with
        | zero => omega
        | succ j =>
            cases xs with
            | nil => rfl
            | cons a xs => cases xs with
              | nil => rfl
              | cons b xs => rfl
  | succ i ih =>
      cases j with
      | zero => omega
      | succ j =>
          cases xs with
          | nil => rfl
          | cons a xs =>
              simpa only [stepList] using
                congrArg (List.cons a) (ih j (by omega) xs)

/-- Operators on the first and last pairs of a genuine triple. -/
def leftTriple (R : PairOperator A) (t : A × A × A) : A × A × A :=
  ((R (t.1, t.2.1)).1, (R (t.1, t.2.1)).2, t.2.2)

def rightTriple (R : PairOperator A) (t : A × A × A) : A × A × A :=
  (t.1, (R (t.2.1, t.2.2)).1, (R (t.2.1, t.2.2)).2)

def YangBaxter (R : PairOperator A) : Prop :=
  ∀ t, leftTriple R (rightTriple R (leftTriple R t)) =
    rightTriple R (leftTriple R (rightTriple R t))

/-- The three-slot lower bound is essential, even for the ordinary flip. -/
theorem stepList_braid (R : PairOperator A) (hR : YangBaxter R)
    (i : Nat) (xs : List A) (h : i + 3 ≤ xs.length) :
    stepList R i (stepList R (i + 1) (stepList R i xs)) =
      stepList R (i + 1) (stepList R i (stepList R (i + 1) xs)) := by
  induction i generalizing xs with
  | zero =>
      cases xs with
      | nil => simp at h
      | cons a xs => cases xs with
        | nil => simp at h
        | cons b xs => cases xs with
          | nil => simp at h
          | cons c xs =>
              exact congrArg (fun t : A × A × A => t.1 :: t.2.1 :: t.2.2 :: xs)
                (hR (a, b, c))
  | succ i ih =>
      cases xs with
      | nil => simp at h
      | cons a xs =>
          have ht : i + 3 ≤ xs.length := by simpa using h
          simpa only [stepList] using congrArg (List.cons a) (ih xs ht)

/-- Inversion lifts independently of Yang--Baxter. -/
theorem stepList_leftInverse (R Q : PairOperator A) (hQR : Function.LeftInverse Q R)
    (i : Nat) (xs : List A) : stepList Q i (stepList R i xs) = xs := by
  induction i generalizing xs with
  | zero =>
      cases xs with
      | nil => rfl
      | cons a xs => cases xs with
        | nil => rfl
        | cons b xs =>
            exact congrArg (fun t : A × A => t.1 :: t.2 :: xs) (hQR (a, b))
  | succ i ih => cases xs <;> simp [stepList, ih]

/-- n generators act on n+1 entries; Fin n excludes the last invalid crossing. -/
def act (R : PairOperator A) {n : Nat} (i : Fin n) : Sized A (n + 1) → Sized A (n + 1) :=
  fun xs => ⟨stepList R i.val xs.val, (stepList_length R i.val xs.val).trans xs.property⟩

theorem act_far (R : PairOperator A) {n : Nat} (i j : Fin n)
    (h : i.val + 1 < j.val) (xs : Sized A (n + 1)) :
    act R j (act R i xs) = act R i (act R j xs) :=
  Subtype.ext (stepList_far R i.val j.val h xs.val)

theorem act_braid (R : PairOperator A) (hR : YangBaxter R) {n : Nat}
    (i j : Fin n) (hij : i.val + 1 = j.val) (xs : Sized A (n + 1)) :
    act R i (act R j (act R i xs)) = act R j (act R i (act R j xs)) := by
  apply Subtype.ext
  change stepList R i.val (stepList R j.val (stepList R i.val xs.val)) =
    stepList R j.val (stepList R i.val (stepList R j.val xs.val))
  rw [← hij]
  apply stepList_braid R hR
  have hlen := xs.property
  have hj := j.isLt
  omega

theorem act_leftInverse (R Q : PairOperator A) (hQR : Function.LeftInverse Q R)
    {n : Nat} (i : Fin n) (xs : Sized A (n + 1)) :
    act Q i (act R i xs) = xs :=
  Subtype.ext (stepList_leftInverse R Q hQR i.val xs.val)

def actEquiv (e : (A × A) ≃ (A × A)) {n : Nat} (i : Fin n) :
    Sized A (n + 1) ≃ Sized A (n + 1) where
  toFun := act e i
  invFun := act e.symm i
  left_inv := act_leftInverse e e.symm e.left_inv i
  right_inv := act_leftInverse e.symm e e.right_inv i

end CausalGeometry.Exchange.LocalOperator
