/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XIII: densities — the mean of a periodic sequence, and counting residues with
prescribed reductions modulo a set of primes (Chinese remainder theorem).
-/
import Mathlib

namespace ArithmeticDynamics

open Finset Filter Topology

theorem periodic_shift (g : ℕ → ℝ) {Q : ℕ} (hg : ∀ m, g (m + Q) = g m) (k x : ℕ) :
    g (k * Q + x) = g x := by
  induction k with
  | zero => simp
  | succ k ihk =>
    have : (k + 1) * Q + x = (k * Q + x) + Q := by ring
    rw [this, hg, ihk]

/-- Partial sums of a periodic sequence over whole periods. -/
theorem sum_range_mul_period (g : ℕ → ℝ) {Q : ℕ} (hg : ∀ m, g (m + Q) = g m) (k : ℕ) :
    ∑ m ∈ range (k * Q), g m = k * ∑ m ∈ range Q, g m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    simp_rw [periodic_shift g hg]
    push_cast
    ring

/-- **Mean of a periodic sequence.**  If `g` has period `Q > 0`, then
`(1/N) ∑_{m<N} g(m) → (1/Q) ∑_{m<Q} g(m)`. -/
theorem tendsto_avg_periodic (g : ℕ → ℝ) {Q : ℕ} (hQ : 0 < Q) (hg : ∀ m, g (m + Q) = g m) :
    Tendsto (fun N : ℕ => (∑ m ∈ range N, g m) / N) atTop
      (𝓝 ((∑ m ∈ range Q, g m) / Q)) := by
  set S := ∑ m ∈ range Q, g m with hS
  set B := ∑ m ∈ range Q, |g m| with hB
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have key : ∀ N : ℕ, |∑ m ∈ range N, g m - N * (S / Q)| ≤ B + |S| := by
    intro N
    have hN := Nat.div_add_mod N Q
    set k := N / Q
    set r := N % Q
    have hr : r < Q := Nat.mod_lt N hQ
    have hsplit : ∑ m ∈ range N, g m = k * S + ∑ m ∈ range r, g m := by
      rw [← hN, mul_comm Q k, sum_range_add, sum_range_mul_period g hg]
      simp_rw [periodic_shift g hg]
      rw [hS]
    have hNr : (N : ℝ) = k * Q + r := by
      have : ((Q * k + r : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast hN
      push_cast at this
      linarith
    have hrem : |∑ m ∈ range r, g m| ≤ B := by
      calc |∑ m ∈ range r, g m| ≤ ∑ m ∈ range r, |g m| := abs_sum_le_sum_abs _ _
        _ ≤ B := sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hr.le)
            (fun _ _ _ => abs_nonneg _)
    have hfrac : |(r : ℝ) * (S / Q)| ≤ |S| := by
      rw [abs_mul, abs_div, abs_of_pos hQr, Nat.abs_cast]
      have : (r : ℝ) / Q ≤ 1 := by
        rw [div_le_one hQr]
        exact_mod_cast hr.le
      calc (r : ℝ) * (|S| / Q) = (r / Q) * |S| := by ring
        _ ≤ 1 * |S| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = |S| := one_mul _
    have e : ∑ m ∈ range N, g m - N * (S / Q) = ∑ m ∈ range r, g m - r * (S / Q) := by
      rw [hsplit, hNr]
      field_simp
      ring
    rw [e]
    calc |∑ m ∈ range r, g m - r * (S / Q)| ≤ |∑ m ∈ range r, g m| + |(r : ℝ) * (S / Q)| :=
          abs_sub _ _
      _ ≤ B + |S| := add_le_add hrem hfrac
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (B + |S|))
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.norm_eq_abs]
  have : (∑ m ∈ range N, g m) / N - S / Q = (∑ m ∈ range N, g m - N * (S / Q)) / N := by
    field_simp
  rw [this, abs_div, abs_of_pos hNr]
  exact div_le_div_of_nonneg_right (key N) hNr.le

/-! ### Counting with the Chinese remainder theorem -/

section CRT

variable (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime)

/-- The product of the primes in `P`, indexed by the subtype. -/
abbrev primorialOf : ℕ := ∏ i : P, (i : ℕ)

include hP in
theorem primorialOf_pos : 0 < primorialOf P :=
  Finset.prod_pos fun i _ => (hP i i.2).pos

theorem dvd_primorialOf {ℓ : ℕ} (hℓ : ℓ ∈ P) : ℓ ∣ primorialOf P := by
  unfold primorialOf
  exact Finset.dvd_prod_of_mem (fun i : P => (i : ℕ)) (mem_univ ⟨ℓ, hℓ⟩)

include hP in
theorem pairwise_coprime_primes :
    Pairwise (Function.onFun Nat.Coprime (fun i : P => (i : ℕ))) := by
  intro i j hij
  exact (Nat.coprime_primes (hP i i.2) (hP j j.2)).mpr (fun h => hij (Subtype.ext h))

include hP in
/-- **Counting residues by their reductions.**  The number of `m < ∏ P` whose reduction modulo
each `ℓ ∈ P` lies in a prescribed set `T ℓ` is `∏_ℓ |T ℓ|`. -/
theorem card_crt (T : ∀ i : P, Finset (ZMod (i : ℕ))) :
    #((range (primorialOf P)).filter (fun m => ∀ i : P, ((m : ℕ) : ZMod (i : ℕ)) ∈ T i))
      = ∏ i : P, #(T i) := by
  classical
  have hQ : NeZero (primorialOf P) := ⟨(primorialOf_pos P hP).ne'⟩
  set e := ZMod.prodEquivPi (fun i : P => (i : ℕ)) (pairwise_coprime_primes P hP) with he
  have happ : ∀ (x : ZMod (primorialOf P)) (i : P), e x i = (ZMod.cast x : ZMod (i : ℕ)) :=
    fun x i => by rw [he]; exact (ZMod.prodEquivPi_apply _ _ x i).trans (ZMod.castHom_apply _)
  -- reindex `range Q` by `ZMod Q`
  have h1 : #((range (primorialOf P)).filter (fun m => ∀ i : P, ((m : ℕ) : ZMod (i : ℕ)) ∈ T i))
      = #(univ.filter (fun x : ZMod (primorialOf P) => ∀ i : P, e x i ∈ T i)) := by
    refine card_bij (fun m _ => (m : ZMod (primorialOf P))) ?_ ?_ ?_
    · intro m hm
      simp only [mem_filter, mem_range] at hm
      simp only [mem_filter, mem_univ, true_and]
      intro i
      rw [happ, ZMod.cast_natCast (dvd_primorialOf P i.2)]
      exact hm.2 i
    · intro a ha b hb hab
      simp only [mem_filter, mem_range] at ha hb
      have := congrArg ZMod.val hab
      rwa [ZMod.val_natCast_of_lt ha.1, ZMod.val_natCast_of_lt hb.1] at this
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
      simp only [mem_filter, mem_range]
      refine ⟨ZMod.val_lt x, fun i => ?_⟩
      have := hx i
      rwa [happ, ← ZMod.natCast_val] at this
  -- transport along the CRT equivalence
  have h2 : #(univ.filter (fun x : ZMod (primorialOf P) => ∀ i : P, e x i ∈ T i))
      = #(Fintype.piFinset T) := by
    refine card_bij (fun x _ => e x) ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      exact Fintype.mem_piFinset.mpr hx
    · intro a _ b _ hab
      exact e.injective hab
    · intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [mem_filter]
      refine ⟨mem_univ _, fun i => ?_⟩
      rw [e.apply_symm_apply]
      exact Fintype.mem_piFinset.mp hy i
  rw [h1, h2, Fintype.card_piFinset]

end CRT

end ArithmeticDynamics
