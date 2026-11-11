/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part IX: exact extremal values of r on the divisors of n, the optimal consensus rate and
the universal 3/5 bound (Theorems 3.2 and 4.3, Corollary 4.5 of the paper).
-/
import Mathlib
import ArithmeticDynamics.Spectrum

namespace ArithmeticDynamics

open ArithmeticFunction

/-- `p < q` are the two smallest prime divisors of `n`. -/
structure TwoSmallest (n p q : ℕ) : Prop where
  hp : p.Prime
  hq : q.Prime
  hpn : p ∣ n
  hqn : q ∣ n
  hlt : p < q
  least : ∀ l : ℕ, l.Prime → l ∣ n → p ≤ l
  second : ∀ l : ℕ, l.Prime → l ∣ n → l ≠ p → q ≤ l

theorem TwoSmallest.primes {n p q : ℕ} (h : TwoSmallest n p q) :
    ∀ l : ℕ, l.Prime → l ∣ n → l = p ∨ q ≤ l := by
  intro l hl hln
  by_cases hlp : l = p
  · exact Or.inl hlp
  · exact Or.inr (h.second l hl hln hlp)

/-- The values of `r` on the divisors `M > 1` of `n`.  By Hölder's formula these are the
normalised non-trivial adjacency eigenvalues of the unitary Cayley graph `X_n`. -/
def DivSet (n : ℕ) : Set ℝ := {x | ∃ M : ℕ, M ∣ n ∧ 1 < M ∧ r M = x}

/-- **Lemma 3.1(i), sharp form.**  The least value is `-1/(p-1)`, `p = minFac n`. -/
theorem isLeast_divSet {n : ℕ} (hn : 2 ≤ n) :
    IsLeast (DivSet n) (-1 / ((n.minFac : ℝ) - 1)) := by
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  refine ⟨⟨n.minFac, Nat.minFac_dvd n, hp.one_lt, r_prime hp⟩, ?_⟩
  rintro x ⟨M, hMn, hM, rfl⟩
  exact r_ge_of_dvd hM hMn

/-- Every `n ≥ 2` that is not a prime power has two smallest distinct prime divisors. -/
theorem exists_twoSmallest {n : ℕ} (hn : 2 ≤ n) (hpp : ¬ IsPrimePow n) :
    ∃ q : ℕ, TwoSmallest n n.minFac q := by
  have hn0 : n ≠ 0 := by omega
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  set p := n.minFac with hpdef
  have hsplit : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  set c := n / p ^ n.factorization p with hcdef
  have hc1 : c ≠ 1 := by
    intro hc
    apply hpp
    rw [isPrimePow_nat_iff]
    refine ⟨p, n.factorization p, hp, ?_, ?_⟩
    · exact hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
    · rw [hc, mul_one] at hsplit
      exact hsplit
  have hq : c.minFac.Prime := Nat.minFac_prime hc1
  have hcn : c ∣ n := Nat.ordCompl_dvd n p
  have hqn : c.minFac ∣ n := dvd_trans (Nat.minFac_dvd c) hcn
  have hpc : ¬ p ∣ c := Nat.not_dvd_ordCompl hp hn0
  have hne : c.minFac ≠ p := by
    intro h
    exact hpc (h ▸ Nat.minFac_dvd c)
  have hle : p ≤ c.minFac := Nat.minFac_le_of_dvd hq.two_le hqn
  refine ⟨c.minFac, hp, hq, Nat.minFac_dvd n, hqn, lt_of_le_of_ne hle (Ne.symm hne), ?_, ?_⟩
  · intro l hl hln
    exact Nat.minFac_le_of_dvd hl.two_le hln
  · intro l hl hln hlp
    have hcop : Nat.Coprime l (p ^ n.factorization p) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hl hp).mpr hlp)
    have hlc : l ∣ c := by
      rw [← hsplit] at hln
      exact hcop.dvd_of_dvd_mul_left hln
    exact Nat.minFac_le_of_dvd hl.two_le hlc

/-- **Lemma 3.1(ii), sharp form.** -/
theorem isGreatest_divSet_of_twoSmallest {n p q : ℕ} (h : TwoSmallest n p q) :
    IsGreatest (DivSet n) (1 / (((p : ℝ) - 1) * ((q : ℝ) - 1))) := by
  have hne : p ≠ q := by have := h.hlt; omega
  have hcop : Nat.Coprime p q := (Nat.coprime_primes h.hp h.hq).mpr hne
  refine ⟨⟨p * q, hcop.mul_dvd_of_dvd_of_dvd h.hpn h.hqn, ?_, r_mul_primes h.hp h.hq hne⟩, ?_⟩
  · have := h.hp.two_le
    have := h.hq.two_le
    nlinarith
  · rintro x ⟨M, hMn, hM, rfl⟩
    exact r_le_of_dvd h.hp h.hq h.hlt h.primes hM hMn

/-- **Lemma 3.1(iii), sharp form.** -/
theorem isGreatest_divSet_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    IsGreatest (DivSet (p ^ a)) 0 := by
  refine ⟨⟨p ^ 2, pow_dvd_pow p ha, ?_, r_prime_sq hp⟩, ?_⟩
  · have := hp.two_le
    nlinarith
  · rintro x ⟨M, hMn, hM, rfl⟩
    exact r_le_zero_of_dvd_prime_pow hp hM hMn

/-- **Lemma 3.1(iv).** -/
theorem isGreatest_divSet_prime {p : ℕ} (hp : p.Prime) :
    IsGreatest (DivSet p) (-1 / ((p : ℝ) - 1)) := by
  refine ⟨⟨p, dvd_rfl, hp.one_lt, r_prime hp⟩, ?_⟩
  rintro x ⟨M, hMn, hM, rfl⟩
  rcases (Nat.dvd_prime hp).mp hMn with h | h
  · omega
  · rw [h, r_prime hp]

/-! ### The optimal consensus rate -/

/-- `(λ_max - λ₂)/(λ_max + λ₂)` expressed through the extreme values `rmax`, `rmin` of `r`,
using `λ = φ(n) (1 - r)`. -/
noncomputable def rateOf (rmax rmin : ℝ) : ℝ := (rmax - rmin) / (2 - rmax - rmin)

theorem rateOf_eq_laplacian (φ rmax rmin : ℝ) (hφ : φ ≠ 0) :
    (φ * (1 - rmin) - φ * (1 - rmax)) / (φ * (1 - rmin) + φ * (1 - rmax)) = rateOf rmax rmin := by
  unfold rateOf
  have h1 : φ * (1 - rmin) - φ * (1 - rmax) = φ * (rmax - rmin) := by ring
  have h2 : φ * (1 - rmin) + φ * (1 - rmax) = φ * (2 - rmax - rmin) := by ring
  rw [h1, h2, mul_div_mul_left _ _ hφ]

/-- **Theorem 4.3, first case.** -/
theorem rateOf_twoSmallest {p q : ℝ} (hp : 2 ≤ p) (hq : 3 ≤ q) :
    rateOf (1 / ((p - 1) * (q - 1))) (-1 / (p - 1)) = q / (2 * (p - 1) * (q - 1) + q - 2) := by
  unfold rateOf
  have hp' : p - 1 ≠ 0 := by linarith
  have hq' : q - 1 ≠ 0 := by linarith
  have hd : 2 * (p - 1) * (q - 1) + q - 2 ≠ 0 := by nlinarith
  have hd' : 2 - 1 / ((p - 1) * (q - 1)) - -1 / (p - 1) ≠ 0 := by
    have e : 2 - 1 / ((p - 1) * (q - 1)) - -1 / (p - 1)
        = (2 * (p - 1) * (q - 1) + q - 2) / ((p - 1) * (q - 1)) := by
      field_simp
      ring
    rw [e]
    exact div_ne_zero hd (mul_ne_zero hp' hq')
  rw [div_eq_div_iff hd' hd]
  field_simp
  ring

/-- **Theorem 4.3, prime-power case.** -/
theorem rateOf_primePow {p : ℝ} (hp : 2 ≤ p) :
    rateOf 0 (-1 / (p - 1)) = 1 / (2 * p - 1) := by
  unfold rateOf
  have hp' : p - 1 ≠ 0 := by linarith
  have hd : 2 * p - 1 ≠ 0 := by linarith
  have hd' : 2 - 0 - -1 / (p - 1) ≠ 0 := by
    have e : 2 - 0 - -1 / (p - 1) = (2 * p - 1) / (p - 1) := by
      field_simp
      ring
    rw [e]
    exact div_ne_zero hd hp'
  rw [div_eq_div_iff hd' hd]
  field_simp
  ring

/-- **Theorem 4.3, prime case.** -/
theorem rateOf_self (x : ℝ) : rateOf x x = 0 := by simp [rateOf]

/-- `ρ*(X_n)` as a relation: `ρ` is the rate determined by the greatest and least
elements of `DivSet n`. -/
def IsRate (n : ℕ) (ρ : ℝ) : Prop :=
  ∃ rmax rmin : ℝ, IsGreatest (DivSet n) rmax ∧ IsLeast (DivSet n) rmin ∧ ρ = rateOf rmax rmin

theorem IsRate.unique {n : ℕ} {ρ ρ' : ℝ} (h : IsRate n ρ) (h' : IsRate n ρ') : ρ = ρ' := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  obtain ⟨a', b', ha', hb', rfl⟩ := h'
  rw [ha.unique ha', hb.unique hb']

/-- **Theorem 4.3** for `n` with at least two prime divisors. -/
theorem isRate_of_twoSmallest {n p q : ℕ} (hn : 2 ≤ n) (h : TwoSmallest n p q) :
    IsRate n ((q : ℝ) / (2 * ((p : ℝ) - 1) * ((q : ℝ) - 1) + q - 2)) := by
  have hpm : p = n.minFac :=
    le_antisymm (h.least _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n))
      (Nat.minFac_le_of_dvd h.hp.two_le h.hpn)
  refine ⟨_, _, isGreatest_divSet_of_twoSmallest h, isLeast_divSet hn, ?_⟩
  rw [← hpm]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast h.hp.two_le
  have hq3 : (3 : ℝ) ≤ q := by
    have : 3 ≤ q := by have := h.hp.two_le; have := h.hlt; omega
    exact_mod_cast this
  exact (rateOf_twoSmallest hp2 hq3).symm

/-- **Theorem 4.3** for proper prime powers. -/
theorem isRate_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    IsRate (p ^ a) (1 / (2 * (p : ℝ) - 1)) := by
  have h2 : 2 ≤ p ^ a := by
    have := hp.two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right (by omega) (by omega)
  have hmin : (p ^ a).minFac = p := Nat.Prime.pow_minFac hp (by omega)
  refine ⟨_, _, isGreatest_divSet_prime_pow hp ha, isLeast_divSet h2, ?_⟩
  rw [hmin]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact (rateOf_primePow hp2).symm

/-- **Theorem 4.3** for primes. -/
theorem isRate_prime {p : ℕ} (hp : p.Prime) : IsRate p 0 := by
  refine ⟨_, _, isGreatest_divSet_prime hp, isLeast_divSet hp.two_le, ?_⟩
  rw [Nat.Prime.minFac_eq hp, rateOf_self]

/-- **Corollary 4.5.**  For every `n ≥ 2` the optimal rate is at most `3/5`, with equality
if and only if `6 ∣ n`. -/
theorem rate_le_and_eq_iff {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} (h : IsRate n ρ) :
    ρ ≤ 3 / 5 ∧ (ρ = 3 / 5 ↔ 6 ∣ n) := by
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have h6 : ¬ 6 ∣ p ^ k := by
      intro h6
      have h2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.prime_two.dvd_of_dvd_pow (dvd_trans (by norm_num) h6))).symm
      have h3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h6))).symm
      omega
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      rw [pow_one] at h h6 ⊢
      have := h.unique (isRate_prime hp)
      subst this
      exact ⟨by norm_num, by constructor <;> intro h' <;> [norm_num at h'; exact absurd h' h6]⟩
    · have := h.unique (isRate_prime_pow hp hk2)
      subst this
      have hlt : 1 / (2 * (p : ℝ) - 1) < 3 / 5 := by
        rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
        linarith
      exact ⟨hlt.le, by constructor <;> intro h' <;> [linarith; exact absurd h' h6]⟩
  · obtain ⟨q, hts⟩ := exists_twoSmallest hn hpp
    have := h.unique (isRate_of_twoSmallest hn hts)
    subst this
    set p := n.minFac with hpdef
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hts.hp.two_le
    have hq3n : 3 ≤ q := by have := hts.hp.two_le; have := hts.hlt; omega
    have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq3n
    have hD : (0 : ℝ) < 2 * ((p : ℝ) - 1) * ((q : ℝ) - 1) + q - 2 := by
      have h0 : 0 ≤ ((p : ℝ) - 2) * ((q : ℝ) - 3) := mul_nonneg (by linarith) (by linarith)
      nlinarith [h0]
    have h0 : 0 ≤ ((p : ℝ) - 2) * ((q : ℝ) - 3) := mul_nonneg (by linarith) (by linarith)
    refine ⟨?_, ?_⟩
    · rw [div_le_div_iff₀ hD (by norm_num)]
      nlinarith [h0]
    · constructor
      · intro heq
        rw [div_eq_div_iff hD.ne' (by norm_num)] at heq
        have hp' : (p : ℝ) = 2 := by nlinarith [h0]
        have hq' : (q : ℝ) = 3 := by nlinarith [h0]
        have hpn : p = 2 := by exact_mod_cast hp'
        have hqn : q = 3 := by exact_mod_cast hq'
        have h2 : 2 ∣ n := hpn ▸ hts.hpn
        have h3 : 3 ∣ n := hqn ▸ hts.hqn
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
      · intro h6
        have h2 : 2 ∣ n := dvd_trans (by norm_num) h6
        have h3 : 3 ∣ n := dvd_trans (by norm_num) h6
        have hpn : p = 2 := le_antisymm (hts.least 2 Nat.prime_two h2) hts.hp.two_le
        have hqn : q = 3 :=
          le_antisymm (hts.second 3 Nat.prime_three h3 (by omega)) hq3n
        rw [hpn, hqn]
        norm_num

/-! ### Link with the spectrum of `X_n` -/

/-- `DivSet n` is exactly the set of normalised non-trivial adjacency eigenvalues
`r(ord k)`, `k ≠ 0`, of the unitary Cayley graph `X_n`; equivalently the Laplacian
eigenvalues attached to `k ≠ 0` are the numbers `φ(n)(1 - x)`, `x ∈ DivSet n`. -/
theorem mem_divSet_iff {n : ℕ} [NeZero n] (x : ℝ) :
    x ∈ DivSet n ↔ ∃ k : ZMod n, k ≠ 0 ∧ r (addOrderOf k) = x := by
  constructor
  · rintro ⟨M, hMn, hM, rfl⟩
    exact ⟨((n / M : ℕ) : ZMod n), natCast_div_ne_zero hMn hM, by rw [addOrderOf_natCast_div hMn]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨addOrderOf k, addOrderOf_dvd_self k, one_lt_addOrderOf hk, rfl⟩

end ArithmeticDynamics
