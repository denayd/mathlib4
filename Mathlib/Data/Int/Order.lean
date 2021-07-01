/-
Ported to Lean4 by Deniz Aydin from here in the lean3 core:
https://github.com/leanprover-community/lean/blob/master/library/init/data/int/order.lean

Original file license:
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order

namespace Int
open Nat

set_option pp.coercions false

lemma lt_iff_add_one_le (a b : ℤ) : a < b ↔ a + 1 ≤ b := Iff.refl _

lemma nonneg.elim {a : ℤ} (h : nonneg a): ∃ n : ℕ, a = ↑n := match a with
| ofNat a => ⟨a, rfl⟩
| negSucc a => by trivial

lemma nonneg_or_nonneg_neg (a : ℤ) : nonneg a ∨ nonneg (-a) := match a with
| ofNat a => Or.inl (NonNeg.mk a)
| negSucc a => Or.inr (NonNeg.mk (succ a))

lemma le.intro_sub {a b : ℤ} {n : ℕ} (h : b - a = n) : a ≤ b :=
show nonneg (b - a) by
  rw [h]
  exact NonNeg.mk n

attribute [local simp] Int.sub_eq_add_neg Int.add_assoc Int.add_right_neg Int.add_left_neg
  Int.zero_add Int.add_zero Int.neg_add Int.neg_neg Int.neg_zero

lemma le.intro {a b : ℤ} {n : ℕ} (h : a + ↑n = b) : a ≤ b :=
@le.intro_sub a b n -- with implicit args I get "motive is not type correct"
(by
  rw [← h, Int.sub_eq_add_neg, Int.add_comm, ← Int.add_assoc (-a) (a) (↑n)]
  simp
  rfl
)

lemma le.dest_sub {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, b - a = ↑n := nonneg.elim h

lemma le.dest {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, a + ↑n = b :=
match (le.dest_sub h) with
| ⟨n, h₁⟩ => Exists.intro n (by
  rw [← h₁, Int.add_comm]
  simp)

lemma le.elim {a b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
Exists.elim (le.dest h) h'

protected lemma le_total (a b : ℤ) : a ≤ b ∨ b ≤ a :=
Or.imp_right
  (λ (H : nonneg (-(b - a))) =>
   have : -(b - a) = a - b := by simp [Int.add_comm]
   show nonneg (a - b) from this ▸ H)
  (nonneg_or_nonneg_neg (b - a))

lemma coe_nat_le_coe_nat_of_le {m n : ℕ} (h : m ≤ n) : (↑m : ℤ) ≤ ↑n :=
match Nat.le.dest h with
| ⟨k, (hk : m + k = n)⟩ => @le.intro ↑m ↑n k (by rw [← hk] rfl)

lemma le_of_coe_nat_le_coe_nat {m n : ℕ} (h : (↑m : ℤ) ≤ ↑n) : m ≤ n :=
le.elim h (λ k (hk : ↑m + ↑k = ↑n) =>
  have : m + k = n := Int.coe_nat_inj ((Int.coe_nat_add m k).trans hk)
  Nat.le.intro this)

lemma coe_nat_le_coe_nat_iff (m n : ℕ) : (↑m : ℤ) ≤ ↑n ↔ m ≤ n :=
Iff.intro le_of_coe_nat_le_coe_nat coe_nat_le_coe_nat_of_le

lemma coe_zero_le (n : ℕ) : 0 ≤ (↑n : ℤ) :=
coe_nat_le_coe_nat_of_le n.zero_le

lemma eq_coe_of_zero_le {a : ℤ} (h : 0 ≤ a) : ∃ n : ℕ, a = ↑n := by
  have t := le.dest_sub h
  simp at t
  exact t

lemma eq_succ_of_zero_lt {a : ℤ} (h : 0 < a) : ∃ n : ℕ, a = ↑n.succ :=
let ⟨n, (h : ↑(1+n) = a)⟩ := le.dest h
⟨n, by rw [Nat.add_comm] at h; exact h.symm⟩

lemma lt_add_succ (a : ℤ) (n : ℕ) : a < a + ↑(succ n) :=
le.intro (show (a + 1) + ↑n = a + succ n
  by {simp [Int.coe_nat_eq, Int.add_comm, Int.add_left_comm] rfl})

lemma lt.intro {a b : ℤ} {n : ℕ} (h : a + ↑(succ n) = b) : a < b :=
h ▸ lt_add_succ a n

lemma lt.dest {a b : ℤ} (h : a < b) : ∃ n : ℕ, a + ↑(succ n) = b :=
le.elim h (λ n (hn : (a + 1) + (↑n) = b) =>
    Exists.intro n (by {rw [← hn, Int.add_assoc, Int.add_comm 1] rfl}))

lemma lt.elim {a b : ℤ} (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(succ n) = b → P) : P :=
Exists.elim (lt.dest h) h'

lemma coe_nat_lt_coe_nat_iff (n m : ℕ) : (↑n : ℤ) < ↑m ↔ n < m := by
  rw [lt_iff_add_one_le, ← Int.coe_nat_succ n, coe_nat_le_coe_nat_iff]
  rfl

lemma lt_of_coe_nat_lt_coe_nat {m n : ℕ} (h : (↑m : ℤ) < ↑n) : m < n :=
(coe_nat_lt_coe_nat_iff  _ _).mp h

lemma coe_nat_lt_coe_nat_of_lt {m n : ℕ} (h : m < n) : (↑m : ℤ) < ↑n :=
(coe_nat_lt_coe_nat_iff _ _).mpr h

/- show that the integers form an ordered additive group -/

protected lemma le_refl (a : ℤ) : a ≤ a :=
le.intro (Int.add_zero a)

protected lemma le_trans {a b c : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
le.elim h₁ (λ n (hn : a + ↑n = b) =>
le.elim h₂ (λ m (hm : b + ↑m = c) =>
(by
  apply le.intro
  rw [← hm, ← hn, Int.add_assoc]
  rfl)))

protected lemma le_antisymm {a b : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
le.elim h₁ (λ n (hn : a + ↑n = b) =>
le.elim h₂ (λ m (hm : b + ↑m = a) =>
  have : a + ↑(n + m) = a + 0 := by rw [Int.coe_nat_add, ← Int.add_assoc, hn, hm, Int.add_zero a]
  have : (↑(n + m) : ℤ) = 0 := Int.add_left_cancel this
  have : n + m = 0 := Int.coe_nat_inj this
  have : n = 0 := Nat.eq_zero_of_add_eq_zero_right this
  show a = b by rw [← hn, this, Int.coe_nat_zero, Int.add_zero a]))

protected lemma lt_irrefl (a : ℤ) : ¬ a < a :=
λ (this : a < a) =>
lt.elim this (λ n (hn : a + succ n = a) =>
  have : a + succ n = a + 0 := by rw [hn, Int.add_zero]
  have : succ n = 0 := Int.coe_nat_inj (Int.add_left_cancel this)
  show False from succ_ne_zero _ this)

protected lemma ne_of_lt {a b : ℤ} (h : a < b) : a ≠ b :=
(λ this : a = b => absurd (by {rw [this] at h; exact h}) (Int.lt_irrefl b))

lemma le_of_lt {a b : ℤ} (h : a < b) : a ≤ b :=
lt.elim h (λ n (hn : a + succ n = b) => le.intro hn)

protected lemma lt_iff_le_and_ne (a b : ℤ) : a < b ↔ (a ≤ b ∧ a ≠ b) :=
Iff.intro
  (λ h => ⟨le_of_lt h, Int.ne_of_lt h⟩)
  (λ ⟨aleb, aneb⟩ =>
    le.elim aleb (λ n (hn : a + ↑n = b) =>
      have : n ≠ 0 :=
        (λ (this : n = 0) => aneb (by rw [← hn, this, Int.coe_nat_zero, Int.add_zero]))
      have : (n = succ (Nat.pred n)) :=
        Eq.symm (succ_pred_eq_of_pos (Nat.pos_of_ne_zero this))
      lt.intro (by rw [this] at hn; exact hn)))

lemma lt_succ (a : ℤ) : a < a + 1 :=
Int.le_refl (a + 1)

protected lemma add_le_add_left {a b : ℤ} (h : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
le.elim h (λ n (hn : a + ↑n = b) =>
  le.intro (show c + a + ↑n = c + b by rw [Int.add_assoc, hn]))

protected lemma add_lt_add_left {a b : ℤ} (h : a < b) (c : ℤ) : c + a < c + b :=
Iff.mpr (Int.lt_iff_le_and_ne _ _)
  (And.intro
    (Int.add_le_add_left (le_of_lt h) _)
    (λ heq => Int.lt_irrefl b (by rw [Int.add_left_cancel heq] at h; exact h)))

protected lemma mul_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
le.elim ha (λ n (hn) =>
le.elim hb (λ m (hm) =>
  le.intro (show 0 + ↑n * ↑m = a * b by rw [← hn, ← hm]; simp [Int.zero_add]; rfl)))

protected lemma mul_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
lt.elim ha (λ n (hn) =>
lt.elim hb (λ m (hm) =>
  lt.intro (show 0 + ↑(succ (succ n * m + n)) = a * b by
    rw [← hn, ← hm]
    simp [Int.coe_nat_zero]
    rw [← Int.coe_nat_mul]
    simp [Nat.mul_succ, succ_add]
    rfl)))

protected lemma zero_lt_one : (0 : ℤ) < 1 := coe_nat_lt_coe_nat_of_lt (Nat.zero_lt_one)

-- What can be done to make this proof look less horrible?
protected lemma lt_iff_le_not_le {a b : ℤ} : a < b ↔ (a ≤ b ∧ ¬ b ≤ a) := by
  simp [Int.lt_iff_le_and_ne] split
  intro h
  { match h with
  | ⟨hab, hn⟩ =>
    split
      assumption
    intro hba
    simp [Int.le_antisymm hab hba] at *}
  { intro h
    match h with
  | ⟨hab, hn⟩ =>
    split
      assumption
    intro h
    simp_all}

instance : LinearOrder Int :=
{ le              := Int.le,
  le_refl         := Int.le_refl,
  le_trans        := @Int.le_trans,
  le_antisymm     := @Int.le_antisymm,
  lt              := Int.lt,
  lt_iff_le_not_le := @Int.lt_iff_le_not_le,
  le_total        := Int.le_total,
  decidable_eq    := Int.decEq,
  decidable_le    := Int.decLe,
  decidable_lt    := Int.decLt }

lemma eq_nat_abs_of_zero_le {a : ℤ} (h : 0 ≤ a) : a = nat_abs a := by
rw [(eq_coe_of_zero_le h).2] rfl

lemma le_nat_abs {a : ℤ} : a ≤ nat_abs a :=
Or.elim
  (λ h => by rw [← eq_nat_abs_of_zero_le h]; apply le_refl)
  (λ h => le_trans h (coe_zero_le _))
  (le_total 0 a)

lemma neg_succ_lt_zero (n : ℕ) : -[1+ n] < 0 :=
lt_of_not_ge $ λ h => let ⟨m, h⟩ := eq_coe_of_zero_le h by contradiction

lemma eq_neg_succ_of_lt_zero : ∀ {a : ℤ}, a < 0 → ∃ n : ℕ, a = -[1+ n]
| (n : ℕ), h => absurd h (not_lt_of_ge (coe_zero_le _))
| -[1+ n], h => ⟨n, rfl⟩

/- int is an ordered add comm group -/

protected lemma eq_neg_of_eq_neg {a b : ℤ} (h : a = -b) : b = -a :=
by rw [h, Int.neg_neg]

protected lemma neg_add_cancel_left (a b : ℤ) : -a + (a + b) = b :=
by rw [← Int.add_assoc, Int.add_left_neg, Int.zero_add]

protected lemma add_neg_cancel_left (a b : ℤ) : a + (-a + b) = b :=
by rw [← Int.add_assoc, Int.add_right_neg, Int.zero_add]

protected lemma add_neg_cancel_right (a b : ℤ) : a + b + -b = a :=
by rw [Int.add_assoc, Int.add_right_neg, Int.add_zero]

protected lemma neg_add_cancel_right (a b : ℤ) : a + -b + b = a :=
by rw [Int.add_assoc, Int.add_left_neg, Int.add_zero]

protected lemma sub_self (a : ℤ) : a - a = 0 :=
by rw [Int.sub_eq_add_neg, Int.add_right_neg]

protected lemma sub_eq_zero_of_eq {a b : ℤ} (h : a = b) : a - b = 0 :=
by rw [h, Int.sub_self]

protected lemma eq_of_sub_eq_zero {a b : ℤ} (h : a - b = 0) : a = b :=
have : 0 + b = b := by rw[Int.zero_add]
have : (a - b) + b = b := by rwa[h]
by rwa [Int.sub_eq_add_neg, Int.neg_add_cancel_right] at this

protected lemma sub_eq_zero_iff_eq {a b : ℤ} : a - b = 0 ↔ a = b :=
⟨Int.eq_of_sub_eq_zero, Int.sub_eq_zero_of_eq⟩

@[simp] protected lemma neg_eq_of_add_eq_zero {a b : ℤ} (h : a + b = 0) : -a = b :=
by rw [← Int.add_zero (-a), ←h, ←Int.add_assoc, Int.add_left_neg, Int.zero_add]

protected lemma neg_mul_eq_neg_mul (a b : ℤ) : -(a * b) = -a * b :=
Int.neg_eq_of_add_eq_zero
  (by rw [← Int.distrib_right, Int.add_right_neg, Int.zero_mul])

protected lemma neg_mul_eq_mul_neg (a b : ℤ) : -(a * b) = a * -b :=
Int.neg_eq_of_add_eq_zero
  (by rw [← Int.distrib_left, Int.add_right_neg, Int.mul_zero])

lemma neg_mul_eq_neg_mul_symm (a b : ℤ) : - a * b = - (a * b) :=
Eq.symm (Int.neg_mul_eq_neg_mul a b)

lemma mul_neg_eq_neg_mul_symm (a b : ℤ) : a * - b = - (a * b) :=
Eq.symm (Int.neg_mul_eq_mul_neg a b)

attribute [local simp] neg_mul_eq_neg_mul_symm mul_neg_eq_neg_mul_symm

protected lemma neg_mul_neg (a b : ℤ) : -a * -b = a * b :=
by simp

protected lemma neg_mul_comm (a b : ℤ) : -a * b = a * -b :=
by simp

protected lemma mul_sub (a b c : ℤ) : a * (b - c) = a * b - a * c :=
by simp [Int.distrib_left a b (-c)]

protected lemma sub_mul (a b c : ℤ) : (a - b) * c = a * c - b * c :=
by simp [Int.distrib_right a (-b) c]

section

protected lemma le_of_add_le_add_left {a b c : ℤ} (h : a + b ≤ a + c) : b ≤ c := by
  have : -a + (a + b) ≤ -a + (a + c) := Int.add_le_add_left h _
  rw [Int.neg_add_cancel_left] at this
  rwa [Int.neg_add_cancel_left] at this

protected lemma lt_of_add_lt_add_left {a b c : ℤ} (h : a + b < a + c) : b < c := by
  have : -a + (a + b) < -a + (a + c) := Int.add_lt_add_left h _
  rw [Int.neg_add_cancel_left] at this
  rwa [Int.neg_add_cancel_left] at this

protected lemma add_le_add_right {a b : ℤ} (h : a ≤ b) (c : ℤ) : a + c ≤ b + c :=
Int.add_comm c a ▸ Int.add_comm c b ▸ Int.add_le_add_left h c

protected theorem add_lt_add_right {a b : ℤ} (h : a < b) (c : ℤ) : a + c < b + c := by
 rw [Int.add_comm a c, Int.add_comm b c]
 exact (Int.add_lt_add_left h c)

protected lemma add_le_add {a b c d : ℤ} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
le_trans (Int.add_le_add_right h₁ c) (Int.add_le_add_left h₂ b)

protected lemma le_add_of_nonneg_right {a b : ℤ} (h : 0 ≤ b) : a ≤ a + b :=
have : a + b ≥ a + 0 := Int.add_le_add_left h a
by rwa [Int.add_zero] at this

protected lemma le_add_of_nonneg_left {a b : ℤ} (h : 0 ≤ b) : a ≤ b + a :=
have : 0 + a ≤ b + a := Int.add_le_add_right h a
by rwa [Int.zero_add] at this

protected lemma add_lt_add {a b c d : ℤ} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
lt_trans (Int.add_lt_add_right h₁ c) (Int.add_lt_add_left h₂ b)

protected lemma add_lt_add_of_le_of_lt {a b c d : ℤ} (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d :=
lt_of_le_of_lt (Int.add_le_add_right h₁ c) (Int.add_lt_add_left h₂ b)

protected lemma add_lt_add_of_lt_of_le {a b c d : ℤ} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
lt_of_lt_of_le (Int.add_lt_add_right h₁ c) (Int.add_le_add_left h₂ b)

protected lemma lt_add_of_pos_right (a : ℤ) {b : ℤ} (h : 0 < b) : a < a + b :=
have : a + 0 < a + b := Int.add_lt_add_left h a
by rwa [Int.add_zero] at this

protected lemma lt_add_of_pos_left (a : ℤ) {b : ℤ} (h : 0 < b) : a < b + a :=
have : 0 + a < b + a := Int.add_lt_add_right h a
by rwa [Int.zero_add] at this

protected lemma le_of_add_le_add_right {a b c : ℤ} (h : a + b ≤ c + b) : a ≤ c :=
Int.le_of_add_le_add_left
  (show b + a ≤ b + c by rwa [Int.add_comm b a, Int.add_comm b c])

protected lemma lt_of_add_lt_add_right {a b c : ℤ} (h : a + b < c + b) : a < c :=
Int.lt_of_add_lt_add_left
  (show b + a < b + c by rwa [Int.add_comm b a, Int.add_comm b c])

-- here we start using properties of zero.
protected lemma add_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
Int.zero_add (0:ℤ) ▸ (Int.add_le_add ha hb)

protected lemma add_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
Int.zero_add (0:ℤ) ▸ (Int.add_lt_add ha hb)

protected lemma add_pos_of_pos_of_nonneg {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
Int.zero_add (0:ℤ) ▸ (Int.add_lt_add_of_lt_of_le ha hb)

protected lemma add_pos_of_nonneg_of_pos {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
Int.zero_add (0:ℤ) ▸ (Int.add_lt_add_of_le_of_lt ha hb)

protected lemma add_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
Int.zero_add (0:ℤ) ▸ (Int.add_le_add ha hb)

protected lemma add_neg {a b : ℤ} (ha : a < 0) (hb : b < 0) : a + b < 0 :=
Int.zero_add (0:ℤ) ▸ (Int.add_lt_add ha hb)

protected lemma add_neg_of_neg_of_nonpos {a b : ℤ} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
Int.zero_add (0:ℤ) ▸ (Int.add_lt_add_of_lt_of_le ha hb)

protected lemma add_neg_of_nonpos_of_neg {a b : ℤ} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
Int.zero_add (0:ℤ) ▸ (Int.add_lt_add_of_le_of_lt ha hb)

protected lemma lt_add_of_le_of_pos {a b c : ℤ} (hbc : b ≤ c) (ha : 0 < a) : b < c + a :=
Int.add_zero b ▸ Int.add_lt_add_of_le_of_lt hbc ha

protected lemma sub_add_cancel (a b : ℤ) : a - b + b = a :=
Int.neg_add_cancel_right a b

protected lemma add_sub_cancel (a b : ℤ) : a + b - b = a :=
Int.add_neg_cancel_right a b

protected lemma add_sub_assoc (a b c : ℤ) : a + b - c = a + (b - c) :=
by rw [Int.sub_eq_add_neg, Int.add_assoc, ←Int.sub_eq_add_neg]

protected lemma neg_le_neg {a b : ℤ} (h : a ≤ b) : -b ≤ -a :=
have : 0 ≤ -a + b := Int.add_left_neg a ▸ Int.add_le_add_left h (-a)
have : 0 + -b ≤ -a + b + -b := Int.add_le_add_right this (-b)
by rwa [Int.add_neg_cancel_right, Int.zero_add] at this

protected lemma le_of_neg_le_neg {a b : ℤ} (h : -b ≤ -a) : a ≤ b :=
suffices -(-a) ≤ -(-b) by
  rwa [Int.neg_neg, Int.neg_neg] at this
Int.neg_le_neg h

protected lemma nonneg_of_neg_nonpos {a : ℤ} (h : -a ≤ 0) : 0 ≤ a :=
have : -a ≤ -0 := by rwa [Int.neg_zero]
Int.le_of_neg_le_neg this

protected lemma neg_nonpos_of_nonneg {a : ℤ} (h : 0 ≤ a) : -a ≤ 0 :=
have : -a ≤ -0 := Int.neg_le_neg h
by rwa [Int.neg_zero] at this

protected lemma nonpos_of_neg_nonneg {a : ℤ} (h : 0 ≤ -a) : a ≤ 0 :=
have : -0 ≤ -a := by rwa [Int.neg_zero]
Int.le_of_neg_le_neg this

protected lemma neg_nonneg_of_nonpos {a : ℤ} (h : a ≤ 0) : 0 ≤ -a :=
have : -0 ≤ -a := Int.neg_le_neg h
by rwa [Int.neg_zero] at this

protected lemma neg_lt_neg {a b : ℤ} (h : a < b) : -b < -a :=
have : 0 < -a + b := Int.add_left_neg a ▸ Int.add_lt_add_left h (-a)
have : 0 + -b < -a + b + -b := Int.add_lt_add_right this (-b)
by rwa [Int.add_neg_cancel_right, Int.zero_add] at this

protected lemma lt_of_neg_lt_neg {a b : ℤ} (h : -b < -a) : a < b :=
Int.neg_neg a ▸ Int.neg_neg b ▸ Int.neg_lt_neg h

protected lemma pos_of_neg_neg {a : ℤ} (h : -a < 0) : 0 < a :=
have : -a < -0 := by rwa [Int.neg_zero]
Int.lt_of_neg_lt_neg this

protected lemma neg_neg_of_pos {a : ℤ} (h : 0 < a) : -a < 0 :=
have : -a < -0 := Int.neg_lt_neg h
by rwa [Int.neg_zero] at this

protected lemma neg_of_neg_pos {a : ℤ} (h : 0 < -a) : a < 0 :=
have : -0 < -a := by rwa [Int.neg_zero]
Int.lt_of_neg_lt_neg this

protected lemma neg_pos_of_neg {a : ℤ} (h : a < 0) : 0 < -a :=
have : -0 < -a := Int.neg_lt_neg h
by rwa [Int.neg_zero] at this

protected lemma le_neg_of_le_neg {a b : ℤ} (h : a ≤ -b) : b ≤ -a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h

protected lemma neg_le_of_neg_le {a b : ℤ} (h : -a ≤ b) : -b ≤ a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h

protected lemma lt_neg_of_lt_neg {a b : ℤ} (h : a < -b) : b < -a := by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h

protected lemma neg_lt_of_neg_lt {a b : ℤ} (h : -a < b) : -b < a := by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h

protected lemma sub_nonneg_of_le {a b : ℤ} (h : b ≤ a) : 0 ≤ a - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected lemma le_of_sub_nonneg {a b : ℤ} (h : 0 ≤ a - b) : b ≤ a := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected lemma sub_nonpos_of_le {a b : ℤ} (h : a ≤ b) : a - b ≤ 0 := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected lemma le_of_sub_nonpos {a b : ℤ} (h : a - b ≤ 0) : a ≤ b := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected lemma sub_pos_of_lt {a b : ℤ} (h : b < a) : 0 < a - b := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected lemma lt_of_sub_pos {a b : ℤ} (h : 0 < a - b) : b < a := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected lemma sub_neg_of_lt {a b : ℤ} (h : a < b) : a - b < 0 := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected lemma lt_of_sub_neg {a b : ℤ} (h : a - b < 0) : a < b := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected lemma add_le_of_le_neg_add {a b c : ℤ} (h : b ≤ -a + c) : a + b ≤ c := by
  have h := Int.add_le_add_left h a
  rwa [Int.add_neg_cancel_left] at h

protected lemma le_neg_add_of_add_le {a b c : ℤ} (h : a + b ≤ c) : b ≤ -a + c := by
  have h := Int.add_le_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h

protected lemma add_le_of_le_sub_left {a b c : ℤ} (h : b ≤ c - a) : a + b ≤ c := by
  have h := Int.add_le_add_left h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h

protected lemma le_sub_left_of_add_le {a b c : ℤ} (h : a + b ≤ c) : b ≤ c - a := by
  have h := Int.add_le_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h

protected lemma add_le_of_le_sub_right {a b c : ℤ} (h : a ≤ c - b) : a + b ≤ c := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel] at h

protected lemma le_sub_right_of_add_le {a b c : ℤ} (h : a + b ≤ c) : a ≤ c - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h

protected lemma le_add_of_neg_add_le {a b c : ℤ} (h : -b + a ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_left h b
  rwa [Int.add_neg_cancel_left] at h

protected lemma neg_add_le_of_le_add {a b c : ℤ} (h : a ≤ b + c) : -b + a ≤ c := by
  have h := Int.add_le_add_left h (-b)
  rwa [Int.neg_add_cancel_left] at h

protected lemma le_add_of_sub_left_le {a b c : ℤ} (h : a - b ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h

protected lemma sub_left_le_of_le_add {a b c : ℤ} (h : a ≤ b + c) : a - b ≤ c := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h

protected lemma le_add_of_sub_right_le {a b c : ℤ} (h : a - c ≤ b) : a ≤ b + c := by
  have h := Int.add_le_add_right h c
  rwa [Int.sub_add_cancel] at h

protected lemma sub_right_le_of_le_add {a b c : ℤ} (h : a ≤ b + c) : a - c ≤ b := by
  have h := Int.add_le_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h

protected lemma le_add_of_neg_add_le_left {a b c : ℤ} (h : -b + a ≤ c) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_left_le h

protected lemma neg_add_le_left_of_le_add {a b c : ℤ} (h : a ≤ b + c) : -b + a ≤ c := by
  rw [Int.add_comm,]
  exact Int.sub_left_le_of_le_add h

protected lemma le_add_of_neg_add_le_right {a b c : ℤ} (h : -c + a ≤ b) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_right_le h

protected lemma neg_add_le_right_of_le_add {a b c : ℤ} (h : a ≤ b + c) : -c + a ≤ b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_le_left_of_le_add h

protected lemma le_add_of_neg_le_sub_left {a b c : ℤ} (h : -a ≤ b - c) : c ≤ a + b :=
Int.le_add_of_neg_add_le_left (Int.add_le_of_le_sub_right h)

protected lemma neg_le_sub_left_of_le_add {a b c : ℤ} (h : c ≤ a + b) : -a ≤ b - c := by
  have h := Int.le_neg_add_of_add_le (Int.sub_left_le_of_le_add h)
  rwa [Int.add_comm] at h

protected lemma le_add_of_neg_le_sub_right {a b c : ℤ} (h : -b ≤ a - c) : c ≤ a + b :=
Int.le_add_of_sub_right_le (Int.add_le_of_le_sub_left h)

protected lemma neg_le_sub_right_of_le_add {a b c : ℤ} (h : c ≤ a + b) : -b ≤ a - c :=
Int.le_sub_left_of_add_le (Int.sub_right_le_of_le_add h)

protected lemma sub_le_of_sub_le {a b c : ℤ} (h : a - b ≤ c) : a - c ≤ b :=
Int.sub_left_le_of_le_add (Int.le_add_of_sub_right_le h)

protected lemma sub_le_sub_left {a b : ℤ} (h : a ≤ b) (c : ℤ) : c - b ≤ c - a :=
Int.add_le_add_left (Int.neg_le_neg h) c

protected lemma sub_le_sub_right {a b : ℤ} (h : a ≤ b) (c : ℤ) : a - c ≤ b - c :=
Int.add_le_add_right h (-c)

protected lemma sub_le_sub {a b c d : ℤ} (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
Int.add_le_add hab (Int.neg_le_neg hcd)

protected lemma add_lt_of_lt_neg_add {a b c : ℤ} (h : b < -a + c) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [Int.add_neg_cancel_left] at h

protected lemma lt_neg_add_of_add_lt {a b c : ℤ} (h : a + b < c) : b < -a + c := by
  have h := Int.add_lt_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h

protected lemma add_lt_of_lt_sub_left {a b c : ℤ} (h : b < c - a) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h

protected lemma lt_sub_left_of_add_lt {a b c : ℤ} (h : a + b < c) : b < c - a := by
  have h := Int.add_lt_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h

protected lemma add_lt_of_lt_sub_right {a b c : ℤ} (h : a < c - b) : a + b < c := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel] at h

protected lemma lt_sub_right_of_add_lt {a b c : ℤ} (h : a + b < c) : a < c - b := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h

protected lemma lt_add_of_neg_add_lt {a b c : ℤ} (h : -b + a < c) : a < b + c := by
  have h := Int.add_lt_add_left h b
  rwa [Int.add_neg_cancel_left] at h

protected lemma neg_add_lt_of_lt_add {a b c : ℤ} (h : a < b + c) : -b + a < c := by
  have h := Int.add_lt_add_left h (-b)
  rwa [Int.neg_add_cancel_left] at h

protected lemma lt_add_of_sub_left_lt {a b c : ℤ} (h : a - b < c) : a < b + c := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h

protected lemma sub_left_lt_of_lt_add {a b c : ℤ} (h : a < b + c) : a - b < c := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h

protected lemma lt_add_of_sub_right_lt {a b c : ℤ} (h : a - c < b) : a < b + c := by
  have h := Int.add_lt_add_right h c
  rwa [Int.sub_add_cancel] at h

protected lemma sub_right_lt_of_lt_add {a b c : ℤ} (h : a < b + c) : a - c < b := by
  have h := Int.add_lt_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h

protected lemma lt_add_of_neg_add_lt_left {a b c : ℤ} (h : -b + a < c) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_left_lt h

protected lemma neg_add_lt_left_of_lt_add {a b c : ℤ} (h : a < b + c) : -b + a < c := by
  rw [Int.add_comm,]
  exact Int.sub_left_lt_of_lt_add h

protected lemma lt_add_of_neg_add_lt_right {a b c : ℤ} (h : -c + a < b) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_right_lt h

protected lemma neg_add_lt_right_of_lt_add {a b c : ℤ} (h : a < b + c) : -c + a < b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_lt_left_of_lt_add h

protected lemma lt_add_of_neg_lt_sub_left {a b c : ℤ} (h : -a < b - c) : c < a + b :=
Int.lt_add_of_neg_add_lt_left (Int.add_lt_of_lt_sub_right h)

protected lemma neg_lt_sub_left_of_lt_add {a b c : ℤ} (h : c < a + b) : -a < b - c := by
  have h := Int.lt_neg_add_of_add_lt (Int.sub_left_lt_of_lt_add h)
  rwa [Int.add_comm] at h

protected lemma lt_add_of_neg_lt_sub_right {a b c : ℤ} (h : -b < a - c) : c < a + b :=
Int.lt_add_of_sub_right_lt (Int.add_lt_of_lt_sub_left h)

protected lemma neg_lt_sub_right_of_lt_add {a b c : ℤ} (h : c < a + b) : -b < a - c :=
Int.lt_sub_left_of_add_lt (Int.sub_right_lt_of_lt_add h)

protected lemma sub_lt_of_sub_lt {a b c : ℤ} (h : a - b < c) : a - c < b :=
Int.sub_left_lt_of_lt_add (Int.lt_add_of_sub_right_lt h)

protected lemma sub_lt_sub_left {a b : ℤ} (h : a < b) (c : ℤ) : c - b < c - a :=
Int.add_lt_add_left (Int.neg_lt_neg h) c

protected lemma sub_lt_sub_right {a b : ℤ} (h : a < b) (c : ℤ) : a - c < b - c :=
Int.add_lt_add_right h (-c)

protected lemma sub_lt_sub {a b c d : ℤ} (hab : a < b) (hcd : c < d) : a - d < b - c :=
Int.add_lt_add hab (Int.neg_lt_neg hcd)

protected lemma sub_lt_sub_of_le_of_lt {a b c d : ℤ} (hab : a ≤ b) (hcd : c < d) : a - d < b - c :=
Int.add_lt_add_of_le_of_lt hab (Int.neg_lt_neg hcd)

protected lemma sub_lt_sub_of_lt_of_le {a b c d : ℤ} (hab : a < b) (hcd : c ≤ d) : a - d < b - c :=
Int.add_lt_add_of_lt_of_le hab (Int.neg_le_neg hcd)

protected lemma sub_le_self (a : ℤ) {b : ℤ} (h : 0 ≤ b) : a - b ≤ a :=
have : a - b ≤ _ := Int.add_le_add_left (Int.neg_nonpos_of_nonneg h) _
by rwa [Int.add_zero] at this

protected lemma sub_lt_self (a : ℤ) {b : ℤ} (h : 0 < b) : a - b < a :=
have : a - b < _ := Int.add_lt_add_left (Int.neg_neg_of_pos h) _
by rwa [Int.add_zero] at this

protected lemma add_le_add_three {a b c d e f : ℤ} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) :
      a + b + c ≤ d + e + f := by
  apply le_trans
  apply Int.add_le_add
  apply Int.add_le_add
  repeat assumption
  apply le_refl

/- missing facts -/

protected lemma mul_lt_mul_of_pos_left {a b c : ℤ}
       (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
have : 0 < b - a       := Int.sub_pos_of_lt h₁
have : 0 < c * (b - a) := Int.mul_pos h₂ this
by
  rw [Int.mul_sub] at this
  exact Int.lt_of_sub_pos this

protected lemma mul_lt_mul_of_pos_right {a b c : ℤ}
      (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
have : 0 < b - a       := Int.sub_pos_of_lt h₁
have : 0 < (b - a) * c := Int.mul_pos this h₂
by
  rw [Int.sub_mul] at this
  exact Int.lt_of_sub_pos this

protected lemma mul_le_mul_of_nonneg_left {a b c : ℤ} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b := by
  by_cases hba : b ≤ a; simp [le_antisymm hba h₁]; apply le_refl
  by_cases hc0 : c ≤ 0; simp [le_antisymm hc0 h₂, Int.zero_mul]
  exact (le_not_le_of_lt (Int.mul_lt_mul_of_pos_left
    (lt_of_le_not_le h₁ hba) (lt_of_le_not_le h₂ hc0))).left

protected lemma mul_le_mul_of_nonneg_right {a b c : ℤ} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c := by
  by_cases hba : b ≤ a; simp [le_antisymm hba h₁]; apply le_refl
  by_cases hc0 : c ≤ 0; simp [le_antisymm hc0 h₂, Int.mul_zero]
  exact (le_not_le_of_lt
    (Int.mul_lt_mul_of_pos_right (lt_of_le_not_le h₁ hba) (lt_of_le_not_le h₂ hc0))).left

-- TODO: there are four variations, depending on which variables we assume to be nonneg
protected lemma mul_le_mul {a b c d : ℤ} (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) :
  a * b ≤ c * d := le_trans
  (Int.mul_le_mul_of_nonneg_right hac nn_b)
  (Int.mul_le_mul_of_nonneg_left hbd nn_c)

protected lemma mul_nonpos_of_nonneg_of_nonpos {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 :=
have h : a * b ≤ a * 0 := Int.mul_le_mul_of_nonneg_left hb ha
by rwa [Int.mul_zero] at h

protected lemma mul_nonpos_of_nonpos_of_nonneg {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 :=
have h : a * b ≤ 0 * b := Int.mul_le_mul_of_nonneg_right ha hb
by rwa [Int.zero_mul] at h

protected lemma mul_lt_mul {a b c d : ℤ} (hac : a < c) (hbd : b ≤ d) (pos_b : 0 < b)
  (nn_c : 0 ≤ c) : a * b < c * d := le_trans
  (Int.mul_lt_mul_of_pos_right hac pos_b)
  (Int.mul_le_mul_of_nonneg_left hbd nn_c)

protected lemma mul_lt_mul' {a b c d : ℤ} (h1 : a ≤ c) (h2 : b < d) (h3 : 0 ≤ b) (h4 : 0 < c) :
       a * b < c * d := lt_of_le_of_lt
   (Int.mul_le_mul_of_nonneg_right h1 h3)
   (Int.mul_lt_mul_of_pos_left h2 h4)

protected lemma mul_neg_of_pos_of_neg {a b : ℤ} (ha : 0 < a) (hb : b < 0) : a * b < 0 :=
have h : a * b < a * 0 := Int.mul_lt_mul_of_pos_left hb ha
by rwa [Int.mul_zero] at h

protected lemma mul_neg_of_neg_of_pos {a b : ℤ} (ha : a < 0) (hb : 0 < b) : a * b < 0 :=
have h : a * b < 0 * b := Int.mul_lt_mul_of_pos_right ha hb
by rwa [Int.zero_mul] at  h

protected lemma mul_le_mul_of_nonpos_right {a b c : ℤ} (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c :=
have : -c ≥ 0              := Int.neg_nonneg_of_nonpos hc
have : b * -c ≤ a * -c     := Int.mul_le_mul_of_nonneg_right h this
have : -(b * c) ≤ -(a * c) := by rwa [← Int.neg_mul_eq_mul_neg, ← Int.neg_mul_eq_mul_neg] at this
Int.le_of_neg_le_neg this

protected lemma mul_nonneg_of_nonpos_of_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b :=
have : 0 * b ≤ a * b := Int.mul_le_mul_of_nonpos_right ha hb
by rwa [Int.zero_mul] at this

protected lemma mul_lt_mul_of_neg_left {a b c : ℤ} (h : b < a) (hc : c < 0) : c * a < c * b :=
have : -c > 0              := Int.neg_pos_of_neg hc
have : -c * b < -c * a     := Int.mul_lt_mul_of_pos_left h this
have : -(c * b) < -(c * a) := by rwa [← Int.neg_mul_eq_neg_mul, ← Int.neg_mul_eq_neg_mul] at this
Int.lt_of_neg_lt_neg this

protected lemma mul_lt_mul_of_neg_right {a b c : ℤ} (h : b < a) (hc : c < 0) : a * c < b * c :=
have : -c > 0              := Int.neg_pos_of_neg hc
have : b * -c < a * -c     := Int.mul_lt_mul_of_pos_right h this
have : -(b * c) < -(a * c) := by rwa [← Int.neg_mul_eq_mul_neg, ← Int.neg_mul_eq_mul_neg] at this
Int.lt_of_neg_lt_neg this

protected lemma mul_pos_of_neg_of_neg {a b : ℤ} (ha : a < 0) (hb : b < 0) : 0 < a * b :=
have : 0 * b < a * b := Int.mul_lt_mul_of_neg_right ha hb
by rwa [Int.zero_mul] at this

protected lemma mul_self_le_mul_self {a b : ℤ} (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
Int.mul_le_mul h2 h2 h1 (le_trans h1 h2)

protected lemma mul_self_lt_mul_self {a b : ℤ} (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
Int.mul_lt_mul' (le_of_lt h2) h2 h1 (lt_of_le_of_lt h1 h2)

/- more facts specific to int -/

theorem of_nat_nonneg (n : ℕ) : 0 ≤ ofNat n := NonNeg.mk n

theorem coe_succ_pos (n : ℕ) : 0 < (succ n : ℤ) :=
coe_nat_lt_coe_nat_of_lt (succ_pos _)

theorem exists_eq_neg_of_nat {a : ℤ} (H : a ≤ 0) : ∃n : ℕ, a = -↑n :=
let ⟨n, h⟩ := eq_coe_of_zero_le (Int.neg_nonneg_of_nonpos H)
⟨n, Int.eq_neg_of_eq_neg h.symm⟩

theorem nat_abs_of_nonneg {a : ℤ} (H : 0 ≤ a) : (nat_abs a : ℤ) = a :=
match a, eq_coe_of_zero_le H with
| _, ⟨n, rfl⟩ => rfl end

theorem of_nat_nat_abs_of_nonpos {a : ℤ} (H : a ≤ 0) : (nat_abs a : ℤ) = -a :=
by rw [← nat_abs_neg, nat_abs_of_nonneg (Int.neg_nonneg_of_nonpos H)]

theorem lt_of_add_one_le {a b : ℤ} (H : a + 1 ≤ b) : a < b := H

theorem add_one_le_of_lt {a b : ℤ} (H : a < b) : a + 1 ≤ b := H

theorem lt_add_one_of_le {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
Int.add_le_add_right H 1

theorem le_of_lt_add_one {a b : ℤ} (H : a < b + 1) : a ≤ b :=
Int.le_of_add_le_add_right H

theorem sub_one_le_of_lt {a b : ℤ} (H : a ≤ b) : a - 1 < b :=
Int.sub_right_lt_of_lt_add $ lt_add_one_of_le H

theorem lt_of_sub_one_le {a b : ℤ} (H : a - 1 < b) : a ≤ b :=
le_of_lt_add_one $ Int.lt_add_of_sub_right_lt H

theorem le_sub_one_of_lt {a b : ℤ} (H : a < b) : a ≤ b - 1 :=
Int.le_sub_right_of_add_le H

theorem lt_of_le_sub_one {a b : ℤ} (H : a ≤ b - 1) : a < b :=
Int.add_le_of_le_sub_right H

theorem sign_of_succ (n : ℕ) : sign (succ n) = 1 := rfl

theorem sign_eq_one_of_pos {a : ℤ} (h : 0 < a) : sign a = 1 :=
match a, eq_succ_of_zero_lt h with
| _, ⟨n, rfl⟩ => rfl

theorem sign_eq_neg_one_of_neg {a : ℤ} (h : a < 0) : sign a = -1 :=
match a, eq_neg_succ_of_lt_zero h with
| _, ⟨n, rfl⟩ => rfl

lemma eq_zero_of_sign_eq_zero : ∀ {a : ℤ}, sign a = 0 → a = 0
| 0, _ => rfl

theorem pos_of_sign_eq_one : ∀ {a : ℤ}, sign a = 1 → 0 < a
| (n+1:ℕ), _ => coe_nat_lt_coe_nat_of_lt (succ_pos _)

theorem neg_of_sign_eq_neg_one : ∀ {a : ℤ}, sign a = -1 → a < 0
| (n+1:ℕ), h => by match h with .
| 0,       h => by match h with .
| -[1+ n], _ => neg_succ_lt_zero _

theorem sign_eq_one_iff_pos (a : ℤ) : sign a = 1 ↔ 0 < a :=
⟨pos_of_sign_eq_one, sign_eq_one_of_pos⟩

theorem sign_eq_neg_one_iff_neg (a : ℤ) : sign a = -1 ↔ a < 0 :=
⟨neg_of_sign_eq_neg_one, sign_eq_neg_one_of_neg⟩

theorem sign_eq_zero_iff_zero (a : ℤ) : sign a = 0 ↔ a = 0 :=
⟨eq_zero_of_sign_eq_zero, λ h => by rw [h, sign_zero]⟩

protected lemma eq_zero_or_eq_zero_of_mul_eq_zero
        {a b : ℤ} (h : a * b = 0) : a = 0 ∨ b = 0 :=
match lt_trichotomy 0 a with
| Or.inl hlt₁          =>
  match lt_trichotomy 0 b with
  | Or.inl hlt₂          =>
    have : 0 < a * b := Int.mul_pos hlt₁ hlt₂
    by rw [h] at this; exact absurd this (lt_irrefl _)
  | Or.inr (Or.inl heq₂) => Or.inr heq₂.symm
  | Or.inr (Or.inr hgt₂) =>
    have : 0 > a * b := Int.mul_neg_of_pos_of_neg hlt₁ hgt₂
    by rw [h] at this; exact absurd this (lt_irrefl _)
| Or.inr (Or.inl heq₁) => Or.inl heq₁.symm
| Or.inr (Or.inr hgt₁) =>
  match lt_trichotomy 0 b with
  | Or.inl hlt₂          =>
    have : 0 > a * b := Int.mul_neg_of_neg_of_pos hgt₁ hlt₂
    by rw [h] at this; exact absurd this (lt_irrefl _)
  | Or.inr (Or.inl heq₂) => Or.inr heq₂.symm
  | Or.inr (Or.inr hgt₂) =>
    have : 0 < a * b := Int.mul_pos_of_neg_of_neg hgt₁ hgt₂
    by rw [h] at this; exact absurd this (lt_irrefl _)


protected lemma eq_of_mul_eq_mul_right {a b c : ℤ} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
have : b * a - c * a = 0 := Int.sub_eq_zero_of_eq h
have : (b - c) * a = 0   := by rw [Int.sub_mul, this]
have : b - c = 0         := (Int.eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha
Int.eq_of_sub_eq_zero this

protected lemma eq_of_mul_eq_mul_left {a b c : ℤ} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
have : a * b - a * c = 0 := Int.sub_eq_zero_of_eq h
have : a * (b - c) = 0   := by rw [Int.mul_sub, this]
have : b - c = 0         := (Int.eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha
Int.eq_of_sub_eq_zero this

theorem eq_one_of_mul_eq_self_left {a b : ℤ} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
Int.eq_of_mul_eq_mul_right Hpos (by rw [Int.one_mul, H])

theorem eq_one_of_mul_eq_self_right {a b : ℤ} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
Int.eq_of_mul_eq_mul_left Hpos (by rw [Int.mul_one, H])

end Int
