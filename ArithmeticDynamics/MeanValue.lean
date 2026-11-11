/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part XIV: the mean value of the optimal consensus rate (Proposition 4.9).
-/
import Mathlib
import ArithmeticDynamics.ConsensusDynamics
import ArithmeticDynamics.Density

namespace ArithmeticDynamics

open Finset Filter Topology
open scoped Classical

/-! ### The rate as a function of `n` -/

/-- The optimal consensus rate `ρ*(X_m)` as a function of `m` (`0` for `m < 2`). -/
noncomputable def rhoStar (m : ℕ) : ℝ :=
  if h : 2 ≤ m then Classical.choose (exists_isRate h) else 0

theorem isRate_rhoStar {m : ℕ} (hm : 2 ≤ m) : IsRate m (rhoStar m) := by
  unfold rhoStar
  rw [dif_pos hm]
  exact Classical.choose_spec (exists_isRate hm)

theorem rhoStar_nonneg (m : ℕ) : 0 ≤ rhoStar m := by
  by_cases hm : 2 ≤ m
  · exact isRate_nonneg (isRate_rhoStar hm)
  · simp [rhoStar, hm]

theorem rhoStar_le (m : ℕ) : rhoStar m ≤ 3 / 5 := by
  by_cases hm : 2 ≤ m
  · exact (rate_le_and_eq_iff hm (isRate_rhoStar hm)).1
  · simp only [rhoStar, hm, dite_false]
    norm_num

/-- `q / (2(p-1)(q-1) + q - 2)`, the rate on integers whose two smallest primes are `p < q`. -/
noncomputable def rateVal (p q : ℕ) : ℝ := (q : ℝ) / (2 * ((p : ℝ) - 1) * ((q : ℝ) - 1) + q - 2)

/-- The natural density `(1/(pq)) ∏_{ℓ < q, ℓ ≠ p} (1 - 1/ℓ)` of the integers whose two smallest
prime divisors are `p < q`. -/
noncomputable def dens (p q : ℕ) : ℝ :=
  1 / ((p : ℝ) * q) * ∏ ℓ ∈ (range q).filter (fun ℓ => ℓ.Prime ∧ ℓ ≠ p), (1 - 1 / (ℓ : ℝ))

/-- The terms of the series (4.7). -/
noncomputable def pairWeight (pq : ℕ × ℕ) : ℝ :=
  if pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 then rateVal pq.1 pq.2 * dens pq.1 pq.2 else 0

theorem rateVal_nonneg_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    0 ≤ rateVal p q ∧ rateVal p q ≤ 3 / 5 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq3 : (3 : ℝ) ≤ q := by
    have : 3 ≤ q := by have := hp.two_le; omega
    exact_mod_cast this
  have hD := rate_denominator_pos hp2 hq3
  unfold rateVal
  refine ⟨div_nonneg (by linarith) hD.le, ?_⟩
  rw [div_le_iff₀ hD]
  have := universal_bound hp2 hq3
  linarith

theorem dens_nonneg (p q : ℕ) : 0 ≤ dens p q := by
  unfold dens
  refine mul_nonneg (by positivity) (prod_nonneg fun ℓ hℓ => ?_)
  have hℓ' := (mem_filter.mp hℓ).2.1
  have : (1 : ℝ) / ℓ ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hℓ'.pos)]
    exact_mod_cast hℓ'.one_lt.le
  linarith

theorem pairWeight_nonneg (pq : ℕ × ℕ) : 0 ≤ pairWeight pq := by
  unfold pairWeight
  split_ifs with h
  · exact mul_nonneg (rateVal_nonneg_le h.1 h.2.1 h.2.2).1 (dens_nonneg _ _)
  · exact le_rfl

/-! ### The sets `A_{p,q}` -/

/-- `m ∈ A_{p,q}`: `p, q ∣ m` and no prime `ℓ < q` other than `p` divides `m`. -/
def InA (p q m : ℕ) : Prop := p ∣ m ∧ q ∣ m ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ < q → ℓ ≠ p → ¬ ℓ ∣ m

theorem inA_iff {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    InA p q m ↔ TwoSmallest m p q := by
  constructor
  · rintro ⟨hpm, hqm, h⟩
    refine ⟨hp, hq, hpm, hqm, hpq, fun ℓ hℓ hℓm => ?_, fun ℓ hℓ hℓm hℓp => ?_⟩
    · by_contra hlt
      exact h ℓ hℓ (by omega) (by omega) hℓm
    · by_contra hlt
      exact h ℓ hℓ (by omega) hℓp hℓm
  · intro h
    refine ⟨h.hpn, h.hqn, fun ℓ hℓ hlt hne hdvd => ?_⟩
    have := h.second ℓ hℓ hdvd hne
    omega

theorem twoSmallest_unique {m p q p' q' : ℕ} (h : TwoSmallest m p q) (h' : TwoSmallest m p' q') :
    p = p' ∧ q = q' := by
  have hpp : p = p' := le_antisymm (h.least p' h'.hp h'.hpn) (h'.least p h.hp h.hpn)
  refine ⟨hpp, le_antisymm ?_ ?_⟩
  · exact h.second q' h'.hq h'.hqn (by have := h'.hlt; omega)
  · exact h'.second q h.hq h.hqn (by have := h.hlt; omega)

theorem rhoStar_eq {m p q : ℕ} (hm : 2 ≤ m) (h : TwoSmallest m p q) : rhoStar m = rateVal p q := by
  have hpm : p = m.minFac :=
    le_antisymm (h.least _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd m))
      (Nat.minFac_le_of_dvd h.hp.two_le h.hpn)
  have h' : TwoSmallest m m.minFac q := hpm ▸ h
  have := (isRate_rhoStar hm).unique (isRate_of_twoSmallest hm h')
  rw [this, rateVal, ← hpm]

/-! ### Truncation at the primes up to `y` -/

/-- The primes `≤ y`. -/
def primesUpTo (y : ℕ) : Finset ℕ := (range (y + 1)).filter Nat.Prime

/-- Pairs of primes `p < q ≤ y`. -/
def pairsUpTo (y : ℕ) : Finset (ℕ × ℕ) :=
  ((range (y + 1)) ×ˢ (range (y + 1))).filter (fun pq => pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2)

theorem mem_pairsUpTo {y : ℕ} {pq : ℕ × ℕ} :
    pq ∈ pairsUpTo y ↔ pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 ∧ pq.2 ≤ y := by
  unfold pairsUpTo
  simp only [mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨_, h2⟩, h3, h4, h5⟩
    exact ⟨h3, h4, h5, by omega⟩
  · rintro ⟨h3, h4, h5, h6⟩
    exact ⟨⟨by omega, by omega⟩, h3, h4, h5⟩

theorem primes_mem {y ℓ : ℕ} (hℓ : ℓ.Prime) (hy : ℓ ≤ y) : ℓ ∈ primesUpTo y := by
  unfold primesUpTo
  simp only [mem_filter, mem_range]
  exact ⟨by omega, hℓ⟩

theorem primesUpTo_prime {y : ℕ} : ∀ ℓ ∈ primesUpTo y, ℓ.Prime := fun ℓ h =>
  (mem_filter.mp h).2

/-- `m` has at most one prime divisor `≤ y` (the exceptional set `E_y`). -/
def InE (y m : ℕ) : Prop := ∀ pq ∈ pairsUpTo y, ¬ InA pq.1 pq.2 m

/-- The truncated rate: the value of `ρ*` determined by the primes `≤ y`. -/
noncomputable def fy (y m : ℕ) : ℝ :=
  ∑ pq ∈ pairsUpTo y, if InA pq.1 pq.2 m then rateVal pq.1 pq.2 else 0

theorem fy_eq_of_mem {y m : ℕ} {pq : ℕ × ℕ} (hmem : pq ∈ pairsUpTo y) (hA : InA pq.1 pq.2 m) :
    fy y m = rateVal pq.1 pq.2 := by
  unfold fy
  rw [sum_eq_single pq]
  · simp [hA]
  · intro pq' hmem' hne
    rw [if_neg]
    intro hA'
    obtain ⟨h1, h2, h3, _⟩ := mem_pairsUpTo.mp hmem
    obtain ⟨h1', h2', h3', _⟩ := mem_pairsUpTo.mp hmem'
    obtain ⟨e1, e2⟩ := twoSmallest_unique ((inA_iff h1 h2 h3).mp hA) ((inA_iff h1' h2' h3').mp hA')
    exact hne (Prod.ext e1.symm e2.symm)
  · intro h
    exact absurd hmem h

theorem fy_eq_zero {y m : ℕ} (hE : InE y m) : fy y m = 0 := by
  unfold fy
  exact sum_eq_zero fun pq hpq => by rw [if_neg (hE pq hpq)]

theorem fy_nonneg_le (y m : ℕ) : 0 ≤ fy y m ∧ fy y m ≤ 3 / 5 := by
  by_cases hE : InE y m
  · rw [fy_eq_zero hE]
    norm_num
  · unfold InE at hE
    push_neg at hE
    obtain ⟨pq, hmem, hA⟩ := hE
    rw [fy_eq_of_mem hmem hA]
    obtain ⟨h1, h2, h3, _⟩ := mem_pairsUpTo.mp hmem
    exact rateVal_nonneg_le h1 h2 h3

/-- The truncation error is controlled by the exceptional set and the two points `0, 1`. -/
theorem abs_rhoStar_sub_fy (y m : ℕ) :
    |rhoStar m - fy y m| ≤ (if InE y m then 1 else 0) + (if m < 2 then 1 else 0) := by
  have h1 := rhoStar_nonneg m
  have h2 := rhoStar_le m
  obtain ⟨h3, h4⟩ := fy_nonneg_le y m
  have hb : |rhoStar m - fy y m| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  by_cases hE : InE y m
  · rw [if_pos hE]
    split_ifs <;> linarith
  · by_cases hm : m < 2
    · rw [if_pos hm]
      split_ifs <;> linarith
    · rw [if_neg hE, if_neg hm]
      unfold InE at hE
      push_neg at hE
      obtain ⟨pq, hmem, hA⟩ := hE
      obtain ⟨h1, h2, h3, _⟩ := mem_pairsUpTo.mp hmem
      rw [fy_eq_of_mem hmem hA, rhoStar_eq (by omega) ((inA_iff h1 h2 h3).mp hA)]
      simp

/-! ### Periodicity modulo the primorial -/

theorem inA_add_period {y p q m Q : ℕ} (hpq : (p, q) ∈ pairsUpTo y)
    (hQ : ∀ ℓ, ℓ.Prime → ℓ ≤ y → ℓ ∣ Q) : InA p q (m + Q) ↔ InA p q m := by
  obtain ⟨hp, hq, hlt, hqy⟩ := mem_pairsUpTo.mp hpq
  have key : ∀ ℓ, ℓ.Prime → ℓ ≤ y → (ℓ ∣ m + Q ↔ ℓ ∣ m) := fun ℓ hℓ hy =>
    Nat.dvd_add_left (hQ ℓ hℓ hy)
  unfold InA
  simp only at hp hq
  rw [key p hp (by omega), key q hq hqy]
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨a, b, fun ℓ hℓ h1 h2 => by rw [← key ℓ hℓ (by omega)]; exact c ℓ hℓ h1 h2⟩
  · rintro ⟨a, b, c⟩
    exact ⟨a, b, fun ℓ hℓ h1 h2 => by rw [key ℓ hℓ (by omega)]; exact c ℓ hℓ h1 h2⟩

/-- The primorial of the primes `≤ y`. -/
abbrev Qy (y : ℕ) : ℕ := primorialOf (primesUpTo y)

theorem Qy_pos (y : ℕ) : 0 < Qy y := primorialOf_pos _ (primesUpTo_prime)

theorem dvd_Qy {y ℓ : ℕ} (hℓ : ℓ.Prime) (hy : ℓ ≤ y) : ℓ ∣ Qy y :=
  dvd_primorialOf _ (primes_mem hℓ hy)

theorem fy_periodic (y m : ℕ) : fy y (m + Qy y) = fy y m := by
  unfold fy
  refine sum_congr rfl fun pq hpq => ?_
  have := inA_add_period (m := m) hpq (fun ℓ hℓ hy => dvd_Qy hℓ hy)
  simp only [this]

theorem inE_periodic (y m : ℕ) : InE y (m + Qy y) ↔ InE y m := by
  unfold InE
  constructor
  · intro h pq hpq hA
    exact h pq hpq ((inA_add_period hpq (fun ℓ hℓ hy => dvd_Qy hℓ hy)).mpr hA)
  · intro h pq hpq hA
    exact h pq hpq ((inA_add_period hpq (fun ℓ hℓ hy => dvd_Qy hℓ hy)).mp hA)

/-! ### Densities of `A_{p,q}` -/

theorem card_ne_zero_zmod {ℓ : ℕ} [NeZero ℓ] :
    #(univ.filter (fun x : ZMod ℓ => x ≠ 0)) = ℓ - 1 := by
  rw [filter_ne', card_erase_of_mem (mem_univ _), card_univ, ZMod.card]

theorem natCast_zmod_eq_zero_iff {ℓ m : ℕ} : ((m : ℕ) : ZMod ℓ) = 0 ↔ ℓ ∣ m :=
  ZMod.natCast_eq_zero_iff m ℓ

/-- **The density of `A_{p,q}`.**  For primes `p < q ≤ y`, the proportion of `m < Q_y` in
`A_{p,q}` is exactly `dens p q`. -/
theorem density_inA {y p q : ℕ} (hpq : (p, q) ∈ pairsUpTo y) :
    (#((range (Qy y)).filter (InA p q)) : ℝ) / (Qy y) = dens p q := by
  obtain ⟨hp, hq, hlt, hqy⟩ := mem_pairsUpTo.mp hpq
  simp only at hp hq hlt hqy
  set P := primesUpTo y with hP
  have hPp : ∀ i : P, NeZero (i : ℕ) := fun i => ⟨(primesUpTo_prime i i.2).ne_zero⟩
  let T : ∀ i : P, Finset (ZMod (i : ℕ)) := fun i =>
    haveI := hPp i
    if (i : ℕ) = p ∨ (i : ℕ) = q then {0}
    else if (i : ℕ) < q then univ.filter (fun x => x ≠ 0) else univ
  have hset : (range (Qy y)).filter (InA p q)
      = (range (primorialOf P)).filter (fun m => ∀ i : P, ((m : ℕ) : ZMod (i : ℕ)) ∈ T i) := by
    ext m
    simp only [mem_filter, mem_range]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨hpm, hqm, hno⟩ i
      haveI := hPp i
      simp only [T]
      split_ifs with h1 h2
      · rcases h1 with h1 | h1
        · rw [mem_singleton, natCast_zmod_eq_zero_iff, h1]; exact hpm
        · rw [mem_singleton, natCast_zmod_eq_zero_iff, h1]; exact hqm
      · rw [mem_filter]
        refine ⟨mem_univ _, fun h0 => hno i (primesUpTo_prime i i.2) h2 ?_
          (natCast_zmod_eq_zero_iff.mp h0)⟩
        intro h
        exact h1 (Or.inl h)
      · exact mem_univ _
    · intro h
      have hpP : p ∈ P := primes_mem hp (by omega)
      have hqP : q ∈ P := primes_mem hq hqy
      refine ⟨?_, ?_, fun ℓ hℓ hℓq hℓp hdvd => ?_⟩
      · have hh := h ⟨p, hpP⟩
        simp only [T, true_or, if_true, mem_singleton] at hh
        exact natCast_zmod_eq_zero_iff.mp hh
      · have hh := h ⟨q, hqP⟩
        simp only [T, or_true, if_true, mem_singleton] at hh
        exact natCast_zmod_eq_zero_iff.mp hh
      · have hℓP : ℓ ∈ P := primes_mem hℓ (by omega)
        have hh := h ⟨ℓ, hℓP⟩
        have hne : ¬ (ℓ = p ∨ ℓ = q) := by omega
        simp only [T, hne, if_false, hℓq, if_true, mem_filter, mem_univ, true_and] at hh
        exact hh (natCast_zmod_eq_zero_iff.mpr hdvd)
  have hcard : ∀ i : P, (#(T i) : ℝ) / (i : ℕ)
      = (if (i : ℕ) = p ∨ (i : ℕ) = q then 1 / ((i : ℕ) : ℝ)
          else if (i : ℕ) < q then 1 - 1 / ((i : ℕ) : ℝ) else 1) := by
    intro i
    haveI := hPp i
    have hi : (0 : ℝ) < ((i : ℕ) : ℝ) := by exact_mod_cast (primesUpTo_prime i i.2).pos
    simp only [T]
    split_ifs
    · simp
    · rw [card_ne_zero_zmod, Nat.cast_sub (primesUpTo_prime i i.2).one_le, Nat.cast_one]
      field_simp
    · rw [card_univ, ZMod.card]
      field_simp
  have hQcast : ((Qy y : ℕ) : ℝ) = ∏ i : P, ((i : ℕ) : ℝ) := by rw [← Nat.cast_prod]
  rw [hset, card_crt P primesUpTo_prime T, hQcast, Nat.cast_prod, ← prod_div_distrib]
  simp_rw [hcard]
  rw [prod_coe_sort P (fun ℓ => if ℓ = p ∨ ℓ = q then 1 / (ℓ : ℝ)
      else if ℓ < q then 1 - 1 / (ℓ : ℝ) else 1)]
  have hsplit : ∀ ℓ : ℕ, (if ℓ = p ∨ ℓ = q then 1 / (ℓ : ℝ) else if ℓ < q then 1 - 1 / (ℓ : ℝ) else 1)
      = (if ℓ = p ∨ ℓ = q then 1 / (ℓ : ℝ) else 1)
        * (if ¬ (ℓ = p ∨ ℓ = q) ∧ ℓ < q then 1 - 1 / (ℓ : ℝ) else 1) := by
    intro ℓ
    by_cases h1 : ℓ = p ∨ ℓ = q
    · simp [h1]
    · by_cases h2 : ℓ < q <;> simp [h1, h2]
  simp_rw [hsplit]
  rw [prod_mul_distrib, ← prod_filter, ← prod_filter]
  have e1 : P.filter (fun ℓ => ℓ = p ∨ ℓ = q) = {p, q} := by
    ext ℓ
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro (rfl | rfl)
      · exact ⟨primes_mem hp (by omega), Or.inl rfl⟩
      · exact ⟨primes_mem hq hqy, Or.inr rfl⟩
  have e2 : P.filter (fun ℓ => ¬ (ℓ = p ∨ ℓ = q) ∧ ℓ < q)
      = (range q).filter (fun ℓ => ℓ.Prime ∧ ℓ ≠ p) := by
    ext ℓ
    simp only [hP, primesUpTo, mem_filter, mem_range]
    constructor
    · rintro ⟨⟨_, h2⟩, h3, h4⟩
      exact ⟨h4, h2, fun h => h3 (Or.inl h)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by omega, h2⟩, by omega, h1⟩
  rw [e1, e2, prod_pair (by omega), dens]
  field_simp

/-- **Average of the truncated rate over a period.** -/
theorem avg_fy (y : ℕ) :
    (∑ m ∈ range (Qy y), fy y m) / (Qy y) = ∑ pq ∈ pairsUpTo y, pairWeight pq := by
  have hQ : (0 : ℝ) < Qy y := by exact_mod_cast Qy_pos y
  unfold fy
  rw [sum_comm, sum_div]
  refine sum_congr rfl fun pq hpq => ?_
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm, mul_div_assoc,
    density_inA (by simpa using hpq)]
  obtain ⟨h1, h2, h3, _⟩ := mem_pairsUpTo.mp hpq
  simp [pairWeight, h1, h2, h3]

theorem sum_pairsUpTo_le (y : ℕ) : ∑ pq ∈ pairsUpTo y, pairWeight pq ≤ 3 / 5 := by
  have hQ : (0 : ℝ) < Qy y := by exact_mod_cast Qy_pos y
  rw [← avg_fy, div_le_iff₀ hQ]
  calc ∑ m ∈ range (Qy y), fy y m ≤ ∑ m ∈ range (Qy y), (3 / 5 : ℝ) :=
        sum_le_sum fun m _ => (fy_nonneg_le y m).2
    _ = 3 / 5 * (Qy y) := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-! ### The exceptional set -/

theorem not_inE_of_two {y m a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a < b) (hby : b ≤ y)
    (ham : a ∣ m) (hbm : b ∣ m) : ¬ InE y m := by
  intro hE
  by_cases hm0 : m = 0
  · subst hm0
    have hb3 : 3 ≤ b := by have := ha.two_le; omega
    refine hE (2, 3) (mem_pairsUpTo.mpr ⟨Nat.prime_two, Nat.prime_three, by norm_num, by omega⟩) ?_
    refine ⟨dvd_zero _, dvd_zero _, fun ℓ hℓ h1 h2 _ => ?_⟩
    have := hℓ.two_le
    omega
  · have hm2 : 2 ≤ m := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) ham
      have := ha.two_le
      omega
    have hpp : ¬ IsPrimePow m := by
      intro hpp
      obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
      have h1 := (Nat.prime_dvd_prime_iff_eq ha hr).mp (ha.dvd_of_dvd_pow ham)
      have h2 := (Nat.prime_dvd_prime_iff_eq hb hr).mp (hb.dvd_of_dvd_pow hbm)
      omega
    obtain ⟨q, hts⟩ := exists_twoSmallest hm2 hpp
    have hpa : m.minFac ≤ a := hts.least a ha ham
    have hqb : q ≤ b := hts.second b hb hbm (by omega)
    have hmem : (m.minFac, q) ∈ pairsUpTo y :=
      mem_pairsUpTo.mpr ⟨hts.hp, hts.hq, hts.hlt, by omega⟩
    exact hE _ hmem ((inA_iff hts.hp hts.hq hts.hlt).mpr hts)

/-- Elements of `E_y`: no prime `≤ y` divides `m`, or exactly one does. -/
theorem inE_cases {y m : ℕ} (hE : InE y m) :
    (∀ ℓ ∈ primesUpTo y, ¬ ℓ ∣ m) ∨
      ∃ p ∈ primesUpTo y, ∀ ℓ ∈ primesUpTo y, (ℓ ∣ m ↔ ℓ = p) := by
  by_cases h : ∃ p ∈ primesUpTo y, p ∣ m
  · obtain ⟨p, hp, hpm⟩ := h
    refine Or.inr ⟨p, hp, fun ℓ hℓ => ⟨fun hℓm => ?_, fun h => h ▸ hpm⟩⟩
    by_contra hne
    have hpy : p ≤ y := by have := (mem_filter.mp hp).1; simp at this; omega
    have hℓy : ℓ ≤ y := by have := (mem_filter.mp hℓ).1; simp at this; omega
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact not_inE_of_two (primesUpTo_prime ℓ hℓ) (primesUpTo_prime p hp) hlt hpy hℓm hpm hE
    · exact not_inE_of_two (primesUpTo_prime p hp) (primesUpTo_prime ℓ hℓ) hlt hℓy hpm hℓm hE
  · push_neg at h
    exact Or.inl h

/-- **The exceptional set is small.**  Its proportion in a period is at most
`e^{-S}(1 + 2S)`, `S = ∑_{p ≤ y} 1/p`. -/
theorem density_inE_le (y : ℕ) :
    (#((range (Qy y)).filter (InE y)) : ℝ) / (Qy y)
      ≤ Real.exp (-∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ)) * (1 + 2 * ∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ)) := by
  set P := primesUpTo y with hP
  have hQ : (0 : ℝ) < Qy y := by exact_mod_cast Qy_pos y
  have hPp : ∀ i : P, NeZero (i : ℕ) := fun i => ⟨(primesUpTo_prime i i.2).ne_zero⟩
  let T0 : ∀ i : P, Finset (ZMod (i : ℕ)) := fun i =>
    haveI := hPp i
    univ.filter (fun x => x ≠ 0)
  let Tp : ℕ → ∀ i : P, Finset (ZMod (i : ℕ)) := fun p i =>
    haveI := hPp i
    if (i : ℕ) = p then {0} else univ.filter (fun x => x ≠ 0)
  set A0 := (range (primorialOf P)).filter (fun m => ∀ i : P, ((m : ℕ) : ZMod (i : ℕ)) ∈ T0 i)
  set Ap := fun p => (range (primorialOf P)).filter
    (fun m => ∀ i : P, ((m : ℕ) : ZMod (i : ℕ)) ∈ Tp p i)
  have hsub : (range (Qy y)).filter (InE y) ⊆ A0 ∪ P.biUnion Ap := by
    intro m hm
    obtain ⟨hmr, hE⟩ := mem_filter.mp hm
    rcases inE_cases hE with h0 | ⟨p, hp, hpm⟩
    · refine mem_union_left _ (mem_filter.mpr ⟨hmr, fun i => ?_⟩)
      haveI := hPp i
      simp only [T0, mem_filter, mem_univ, true_and, ne_eq, natCast_zmod_eq_zero_iff]
      exact h0 i i.2
    · refine mem_union_right _ (mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hmr, fun i => ?_⟩⟩)
      haveI := hPp i
      simp only [Tp]
      split_ifs with hip
      · rw [mem_singleton, natCast_zmod_eq_zero_iff]
        exact (hpm i i.2).mpr hip
      · simp only [mem_filter, mem_univ, true_and, ne_eq, natCast_zmod_eq_zero_iff]
        exact fun h => hip ((hpm i i.2).mp h)
  have hQcast : ((Qy y : ℕ) : ℝ) = ∏ i : P, ((i : ℕ) : ℝ) := by rw [← Nat.cast_prod]
  have hc0 : (#A0 : ℝ) / (Qy y) = ∏ ℓ ∈ P, (1 - 1 / (ℓ : ℝ)) := by
    rw [card_crt P primesUpTo_prime T0, hQcast, Nat.cast_prod, ← prod_div_distrib, ← prod_coe_sort P (fun ℓ => 1 - 1 / (ℓ : ℝ))]
    refine prod_congr rfl fun i _ => ?_
    haveI := hPp i
    simp only [T0]
    rw [card_ne_zero_zmod, Nat.cast_sub (primesUpTo_prime i i.2).one_le, Nat.cast_one]
    have hi : ((i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (primesUpTo_prime i i.2).ne_zero
    field_simp
  have hcp : ∀ p ∈ P, (#(Ap p) : ℝ) / (Qy y)
      = ∏ ℓ ∈ P, (if ℓ = p then 1 / (ℓ : ℝ) else 1 - 1 / (ℓ : ℝ)) := by
    intro p _
    rw [card_crt P primesUpTo_prime (Tp p), hQcast, Nat.cast_prod, ← prod_div_distrib,
      ← prod_coe_sort P (fun ℓ => if ℓ = p then 1 / (ℓ : ℝ) else 1 - 1 / (ℓ : ℝ))]
    refine prod_congr rfl fun i _ => ?_
    haveI := hPp i
    have hi : ((i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (primesUpTo_prime i i.2).ne_zero
    simp only [Tp]
    split_ifs
    · simp
    · rw [card_ne_zero_zmod, Nat.cast_sub (primesUpTo_prime i i.2).one_le, Nat.cast_one]
      field_simp
  set E := ∏ ℓ ∈ P, (1 - 1 / (ℓ : ℝ)) with hEdef
  set S := ∑ ℓ ∈ P, 1 / (ℓ : ℝ) with hSdef
  have hfac : ∀ ℓ ∈ P, 0 ≤ 1 - 1 / (ℓ : ℝ) := by
    intro ℓ hℓ
    have hℓ' := primesUpTo_prime ℓ hℓ
    have : (1 : ℝ) / ℓ ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hℓ'.pos)]
      exact_mod_cast hℓ'.one_lt.le
    linarith
  have hE0 : 0 ≤ E := prod_nonneg hfac
  have hEexp : E ≤ Real.exp (-S) := by
    rw [hSdef, ← sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod₀ (h0 := hfac) (h1 := fun ℓ _ => by
      have := Real.one_sub_le_exp_neg (1 / (ℓ : ℝ))
      simpa using this)
  have hterm : ∀ p ∈ P, ∏ ℓ ∈ P, (if ℓ = p then 1 / (ℓ : ℝ) else 1 - 1 / (ℓ : ℝ))
      ≤ 2 * (1 / (p : ℝ)) * E := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (primesUpTo_prime p hp).two_le
    rw [← mul_prod_erase P _ hp, hEdef, ← mul_prod_erase P _ hp]
    have hR : ∏ ℓ ∈ P.erase p, (if ℓ = p then 1 / (ℓ : ℝ) else 1 - 1 / (ℓ : ℝ))
        = ∏ ℓ ∈ P.erase p, (1 - 1 / (ℓ : ℝ)) :=
      prod_congr rfl fun ℓ hℓ => by rw [if_neg (ne_of_mem_erase hℓ)]
    rw [hR, if_pos rfl]
    have hR0 : 0 ≤ ∏ ℓ ∈ P.erase p, (1 - 1 / (ℓ : ℝ)) :=
      prod_nonneg fun ℓ hℓ => hfac ℓ (mem_of_mem_erase hℓ)
    have hk : 1 / (p : ℝ) ≤ 2 * (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) := by
      have h1 : 0 < 1 / (p : ℝ) := by positivity
      have h2 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      nlinarith
    calc 1 / (p : ℝ) * ∏ ℓ ∈ P.erase p, (1 - 1 / (ℓ : ℝ))
        ≤ 2 * (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) * ∏ ℓ ∈ P.erase p, (1 - 1 / (ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_right hk hR0
      _ = 2 * (1 / (p : ℝ)) * ((1 - 1 / (p : ℝ)) * ∏ ℓ ∈ P.erase p, (1 - 1 / (ℓ : ℝ))) := by ring
  have hcount : (#((range (Qy y)).filter (InE y)) : ℝ)
      ≤ (#A0 : ℝ) + ∑ p ∈ P, (#(Ap p) : ℝ) := by
    have h1 := card_le_card hsub
    have h2 := card_union_le A0 (P.biUnion Ap)
    have h3 := card_biUnion_le (s := P) (t := Ap)
    have : #((range (Qy y)).filter (InE y)) ≤ #A0 + ∑ p ∈ P, #(Ap p) := by omega
    exact_mod_cast this
  calc (#((range (Qy y)).filter (InE y)) : ℝ) / (Qy y)
      ≤ ((#A0 : ℝ) + ∑ p ∈ P, (#(Ap p) : ℝ)) / (Qy y) :=
        div_le_div_of_nonneg_right hcount hQ.le
    _ = E + ∑ p ∈ P, (#(Ap p) : ℝ) / (Qy y) := by rw [add_div, sum_div, hc0]
    _ ≤ E + ∑ p ∈ P, 2 * (1 / (p : ℝ)) * E := by
        gcongr with p hp
        rw [hcp p hp]
        exact hterm p hp
    _ = E * (1 + 2 * S) := by rw [← sum_mul, ← mul_sum, hSdef]; ring
    _ ≤ Real.exp (-S) * (1 + 2 * S) := by
        have : 0 ≤ 1 + 2 * S := by
          have : 0 ≤ S := sum_nonneg fun ℓ _ => by positivity
          linarith
        exact mul_le_mul_of_nonneg_right hEexp this

/-- The sum of `1/p` over the primes `≤ y` tends to infinity. -/
theorem tendsto_sum_primes_inv :
    Tendsto (fun y : ℕ => ∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ)) atTop atTop := by
  set f : ℕ → ℝ := Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => Set.indicator_nonneg (fun _ _ => by positivity) _
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).mp not_summable_one_div_on_primes
  have h' := h.comp (tendsto_add_atTop_nat 1)
  refine h'.congr fun y => ?_
  simp only [Function.comp_apply, primesUpTo, sum_filter, hf, Set.indicator_apply,
    Set.mem_setOf_eq]

theorem tendsto_bound_zero :
    Tendsto (fun y : ℕ => Real.exp (-∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ))
      * (1 + 2 * ∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ))) atTop (𝓝 0) := by
  have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hB : Tendsto (fun x : ℝ => Real.exp (-x) * (1 + 2 * x)) atTop (𝓝 0) := by
    have := h0.add (h1.const_mul 2)
    simp only [pow_zero, one_mul, pow_one, mul_zero, add_zero] at this
    refine this.congr fun x => ?_
    ring
  exact hB.comp tendsto_sum_primes_inv

/-! ### Summability and the main theorem -/

/-- The grid `[0, y]²`. -/
def grid (y : ℕ) : Finset (ℕ × ℕ) := (range (y + 1)) ×ˢ (range (y + 1))

theorem sum_grid (y : ℕ) : ∑ pq ∈ grid y, pairWeight pq = ∑ pq ∈ pairsUpTo y, pairWeight pq := by
  unfold pairsUpTo grid
  rw [sum_filter]
  refine sum_congr rfl fun pq _ => ?_
  unfold pairWeight
  split_ifs <;> simp_all

theorem summable_pairWeight : Summable pairWeight := by
  refine summable_of_sum_le (c := 3 / 5) (fun pq => pairWeight_nonneg pq) fun u => ?_
  set y := u.sup (fun pq => pq.1 + pq.2)
  have hsub : u ⊆ grid y := by
    intro pq hpq
    have := le_sup (f := fun pq : ℕ × ℕ => pq.1 + pq.2) hpq
    simp only [grid, mem_product, mem_range]
    constructor <;> omega
  calc ∑ pq ∈ u, pairWeight pq ≤ ∑ pq ∈ grid y, pairWeight pq :=
        sum_le_sum_of_subset_of_nonneg hsub fun pq _ _ => pairWeight_nonneg pq
    _ = ∑ pq ∈ pairsUpTo y, pairWeight pq := sum_grid y
    _ ≤ 3 / 5 := sum_pairsUpTo_le y

/-- The mean value `ρ̄ = ∑_{p<q} (1/(pq)) ∏_{ℓ<q, ℓ≠p} (1 - 1/ℓ) · q/(2(p-1)(q-1)+q-2)`. -/
noncomputable def meanRate : ℝ := ∑' pq, pairWeight pq

theorem tendsto_partial_meanRate :
    Tendsto (fun y => ∑ pq ∈ pairsUpTo y, pairWeight pq) atTop (𝓝 meanRate) := by
  have hmono : Monotone grid := by
    intro a b hab
    exact product_subset_product (range_subset_range.mpr (by omega))
      (range_subset_range.mpr (by omega))
  have hcover : ∀ pq : ℕ × ℕ, ∃ y, pq ∈ grid y := fun pq =>
    ⟨pq.1 + pq.2, by simp only [grid, mem_product, mem_range]; constructor <;> omega⟩
  have := summable_pairWeight.hasSum.comp (tendsto_atTop_finset_of_monotone hmono hcover)
  exact this.congr fun y => sum_grid y

/-- **Proposition 4.9 (mean value of the optimal consensus rate).**  The series defining
`meanRate` converges, and `(1/N) ∑_{n<N} ρ*(X_n) → meanRate`. -/
theorem mean_value :
    Summable pairWeight ∧
      Tendsto (fun N : ℕ => (∑ m ∈ range N, rhoStar m) / N) atTop (𝓝 meanRate) := by
  refine ⟨summable_pairWeight, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose the truncation level `y`
  have hy1 := (Metric.tendsto_atTop.mp tendsto_bound_zero) (ε / 4) (by positivity)
  have hy2 := (Metric.tendsto_atTop.mp tendsto_partial_meanRate) (ε / 4) (by positivity)
  obtain ⟨y1, hy1⟩ := hy1
  obtain ⟨y2, hy2⟩ := hy2
  set y := max y1 y2
  have hb := hy1 y (le_max_left _ _)
  have ha := hy2 y (le_max_right _ _)
  rw [Real.dist_eq, sub_zero] at hb
  rw [Real.dist_eq] at ha
  set bnd := Real.exp (-∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ)) * (1 + 2 * ∑ ℓ ∈ primesUpTo y, 1 / (ℓ : ℝ))
  have hbnd : bnd < ε / 4 := lt_of_le_of_lt (le_abs_self _) hb
  -- averages along `N` for this `y`
  set A := ∑ pq ∈ pairsUpTo y, pairWeight pq
  set D := (#((range (Qy y)).filter (InE y)) : ℝ) / (Qy y)
  have hD : D ≤ bnd := density_inE_le y
  have hG := tendsto_avg_periodic (fy y) (Qy_pos y) (fy_periodic y)
  rw [avg_fy] at hG
  have hH := tendsto_avg_periodic (fun m => if InE y m then (1 : ℝ) else 0) (Qy_pos y)
    (fun m => by simp only [inE_periodic])
  have hHval : (∑ m ∈ range (Qy y), (if InE y m then (1 : ℝ) else 0)) / (Qy y) = D := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  rw [hHval] at hH
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hG) (ε / 4) (by positivity)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hH) (ε / 8) (by positivity)
  obtain ⟨N3, hN3⟩ := (Metric.tendsto_atTop.mp (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)))
    (ε / 8) (by positivity)
  refine ⟨max (max N1 N2) (max N3 1), fun N hN => ?_⟩
  have h1 := hN1 N (by omega)
  have h2 := hN2 N (by omega)
  have h3 := hN3 N (by omega)
  rw [Real.dist_eq] at h1 h2 h3 ⊢
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  -- the truncation error
  have htr : |(∑ m ∈ range N, rhoStar m) / N - (∑ m ∈ range N, fy y m) / N|
      ≤ (∑ m ∈ range N, (if InE y m then (1 : ℝ) else 0)) / N + 2 / N := by
    rw [← sub_div, abs_div, abs_of_pos hNpos, ← sum_sub_distrib]
    have hsmall : ∑ m ∈ range N, (if m < 2 then (1 : ℝ) else 0) ≤ 2 := by
      rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
      have : #((range N).filter (fun m => m < 2)) ≤ 2 := by
        calc #((range N).filter (fun m => m < 2)) ≤ #(range 2) := by
              apply card_le_card
              intro m hm
              simp only [mem_filter, mem_range] at hm ⊢
              exact hm.2
          _ = 2 := card_range 2
      exact_mod_cast this
    calc |∑ m ∈ range N, (rhoStar m - fy y m)| / N
        ≤ (∑ m ∈ range N, ((if InE y m then (1 : ℝ) else 0) + (if m < 2 then 1 else 0))) / N := by
          apply div_le_div_of_nonneg_right _ hNpos.le
          exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => abs_rhoStar_sub_fy y m)
      _ ≤ (∑ m ∈ range N, (if InE y m then (1 : ℝ) else 0)) / N + 2 / N := by
          rw [sum_add_distrib, add_div]
          exact add_le_add le_rfl (div_le_div_of_nonneg_right hsmall hNpos.le)
  have h2' : (∑ m ∈ range N, (if InE y m then (1 : ℝ) else 0)) / N < D + ε / 8 := by
    have := (abs_lt.mp h2).2
    linarith
  have h3' : 2 / (N : ℝ) < ε / 8 := by
    have := (abs_lt.mp h3).2
    linarith
  calc |(∑ m ∈ range N, rhoStar m) / N - meanRate|
      ≤ |(∑ m ∈ range N, rhoStar m) / N - (∑ m ∈ range N, fy y m) / N|
        + |(∑ m ∈ range N, fy y m) / N - A| + |A - meanRate| := by
        have := abs_sub_le ((∑ m ∈ range N, rhoStar m) / N) ((∑ m ∈ range N, fy y m) / N) A
        have := abs_sub_le ((∑ m ∈ range N, rhoStar m) / N) A meanRate
        linarith
    _ < ε := by linarith

end ArithmeticDynamics
