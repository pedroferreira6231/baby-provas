/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 359

*Reference:* [erdosproblems.com/359](https://www.erdosproblems.com/359)
-/

@[expose] public section

namespace Erdos359

open Filter Asymptotics

/-- The predicate that `A` is monotone, `A 0 = n` and for all `j`, `A (j + 1)` is the smallest natural number that
cannot be written as a sum of consecutive terms of `A 0, ..., A j` -/
def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop := A 0 = n ∧ StrictMono A ∧
  ∀ j, IsLeast
    {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
    (A <| j + 1)

/-- Let $a_1< a_2 < ⋯ $ be an infinite sequence of integers such that $a_1=1$ and $a_{i+1}$ is the
least integer which is not a sum of consecutive earlier $a_j$s. Show that $a_k / k \to \infty$. -/
@[category research open, AMS 11]
theorem erdos_359.parts.i (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    atTop.Tendsto (fun k ↦ (A k : ℝ) / k) atTop := by
  sorry

/-- Let $a_1< a_2 < ⋯ $ be an infinite sequence of integers such that $a_1=1$ and $a_{i+1}$ is the
least integer which is not a sum of consecutive earlier $a_j$s. Show that $a_k / k ^ {1 + c} \to 0$
for any $c > 0$. -/
@[category research open, AMS 11]
theorem erdos_359.parts.ii (A : ℕ → ℕ) (hA : IsGoodFor A 1) (c : ℝ) (hc : 0 < c):
    atTop.Tendsto (fun k ↦ A k / (k : ℝ) ^ (1 + c)) (nhds 0) := by
  sorry

def erdos359Vals : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 8
  | 5 => 10
  | 6 => 14
  | 7 => 15
  | _ => 0

theorem erdos359_step (A : ℕ → ℕ) (hA : IsGoodFor A 1) (j v : ℕ)
    (hj : ∀ i ≤ j, A i = erdos359Vals i)
    (hlt : erdos359Vals j < v)
    (hnot : ∀ a ≤ j, ∀ b ≤ j, a ≤ b → v ≠ ∑ i ∈ Finset.Icc a b, erdos359Vals i)
    (hmin : ∀ m < v, erdos359Vals j < m →
      ∃ a ≤ j, ∃ b ≤ j, a ≤ b ∧ m = ∑ i ∈ Finset.Icc a b, erdos359Vals i) :
    A (j + 1) = v := by
  have hsum : ∀ a b, b ≤ j →
      ∑ i ∈ Finset.Icc a b, A i = ∑ i ∈ Finset.Icc a b, erdos359Vals i := by
    intro a b hb
    apply Finset.sum_congr rfl
    intro i hi
    exact hj i ((Finset.mem_Icc.mp hi).2.trans hb)
  have hAj : A j = erdos359Vals j := hj j le_rfl
  have hv : IsLeast
      {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i} v := by
    refine ⟨⟨by rw [hAj]; exact hlt, ?_⟩, ?_⟩
    · intro a b hab
      by_cases h : a ≤ b
      · have hb : b ≤ j := Finset.mem_Iic.mp (hab (Finset.right_mem_Icc.mpr h))
        rw [hsum a b hb]
        exact hnot a (h.trans hb) b hb h
      · rw [Finset.Icc_eq_empty h, Finset.sum_empty]
        omega
    · rintro m ⟨hm1, hm2⟩
      by_contra hcon
      push_neg at hcon
      obtain ⟨a, ha, b, hb, hab, hm⟩ := hmin m hcon (by rw [← hAj]; exact hm1)
      apply hm2 a b
      · intro i hi
        exact Finset.mem_Iic.mpr ((Finset.mem_Icc.mp hi).2.trans hb)
      · rw [hsum a b hb]
        exact hm
  exact (hA.2.2 j).unique hv

/-- Suppose monotone sequence $A$ satisfies the following: `A 0 = 1` and for all `j`, `A (j + 1)` is the
smallest natural number that cannot be written as a sum of consecutive terms of `A 0, ..., A j`.
Then the first few terms of $A$ are $1,2,4,5,8,10,14,15,...$. -/
@[category test, AMS 11]
theorem erdos_359.variants.isGoodFor_1_low_values (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    A '' (Set.Iic 7) = {1, 2, 4, 5, 8, 10, 14, 15} := by
  have h0 : A 0 = 1 := hA.1
  have e1 : A 1 = 2 := erdos359_step A hA 0 2
    (by intro i hi; interval_cases i <;> simp only [h0] <;> first | rfl | decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have e2 : A 2 = 4 := erdos359_step A hA 1 4
    (by intro i hi; interval_cases i <;> simp only [h0, e1] <;> first | rfl | decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have e3 : A 3 = 5 := erdos359_step A hA 2 5
    (by intro i hi; interval_cases i <;> simp only [h0, e1, e2] <;> first | rfl | decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have e4 : A 4 = 8 := erdos359_step A hA 3 8
    (by intro i hi; interval_cases i <;> simp only [h0, e1, e2, e3] <;> first | rfl | decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have e5 : A 5 = 10 := erdos359_step A hA 4 10
    (by intro i hi; interval_cases i <;> simp only [h0, e1, e2, e3, e4] <;> first | rfl | decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have e6 : A 6 = 14 := erdos359_step A hA 5 14
    (by intro i hi; interval_cases i <;> simp only [h0, e1, e2, e3, e4, e5] <;> first | rfl | decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have e7 : A 7 = 15 := erdos359_step A hA 6 15
    (by intro i hi; interval_cases i <;> simp only [h0, e1, e2, e3, e4, e5, e6] <;> first | rfl | decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  ext x
  simp only [Set.mem_image, Set.mem_Iic, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> simp [h0, e1, e2, e3, e4, e5, e6, e7]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by norm_num, h0⟩
    · exact ⟨1, by norm_num, e1⟩
    · exact ⟨2, by norm_num, e2⟩
    · exact ⟨3, by norm_num, e3⟩
    · exact ⟨4, by norm_num, e4⟩
    · exact ⟨5, by norm_num, e5⟩
    · exact ⟨6, by norm_num, e6⟩
    · exact ⟨7, by norm_num, e7⟩

#print axioms erdos_359.variants.isGoodFor_1_low_values


/-- Suppose monotone sequence $A$ satisfies the following: `A 0 = 1` and for all `j`, `A (j + 1)` is the
smallest natural number that cannot be written as a sum of consecutive terms of `A 0, ..., A j`.
Then it is conjectured that $$a_k ~ \frac{k \log k}{\log \log k}$$. -/
@[category research open, AMS 11]
theorem erdos_359.variants.isGoodFor_1_asymptotic (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    (fun k ↦ (A k : ℝ)) ~[atTop] (fun k ↦ k * (k : ℝ).log / (k : ℝ).log.log) := by
  sorry

end Erdos359
