/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part VI: the spectrum of the unitary Cayley graph `X_n` (Theorem 3.2) and the exact
consensus rate (Theorem 4.3).
-/
import Mathlib
import ArithmeticDynamics.Consensus
import ArithmeticDynamics.Ramanujan

namespace ArithmeticDynamics

open Finset

variable (n : ℕ) [NeZero n]

/-- The unitary Cayley graph `X_n`: `a ∼ b` iff `a ≠ b` and `b - a` is a unit of `ℤ/n`. -/
def unitaryCayley : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (fun a b => IsUnit (b - a))

omit [NeZero n] in
theorem unitaryCayley_adj (a b : ZMod n) :
    (unitaryCayley n).Adj a b ↔ a ≠ b ∧ IsUnit (b - a) := by
  unfold unitaryCayley
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hab, h | h⟩
    · exact ⟨hab, h⟩
    · refine ⟨hab, ?_⟩
      have : b - a = -(a - b) := by ring
      rw [this]
      exact h.neg
  · rintro ⟨hab, h⟩
    exact ⟨hab, Or.inl h⟩

/-- The adjacency operator of `X_n` acting on functions `ℤ/n → ℂ`. -/
noncomputable def adj (f : ZMod n → ℂ) (i : ZMod n) : ℂ := ∑ u : (ZMod n)ˣ, f (i + u)

/-- The Laplacian operator `L = φ(n) I - A` of `X_n`. -/
noncomputable def lap (f : ZMod n → ℂ) (i : ZMod n) : ℂ :=
  (Nat.totient n : ℂ) * f i - adj n f i

open Classical in
/-- `adj` is the adjacency operator of the simple graph `X_n` (for `n ≥ 2`). -/
theorem adj_eq_sum_neighbors (hn : 1 < n) (f : ZMod n → ℂ) (i : ZMod n) :
    adj n f i = ∑ j ∈ univ.filter (fun j => (unitaryCayley n).Adj i j), f j := by
  have : Fact (1 < n) := ⟨hn⟩
  unfold adj
  refine sum_bij (fun u _ => i + (u : ZMod n)) ?_ ?_ ?_ ?_
  · intro u _
    refine mem_filter.mpr ⟨mem_univ _, (unitaryCayley_adj n _ _).mpr ⟨?_, ?_⟩⟩
    · intro h
      have : (u : ZMod n) = 0 := by
        have h' : i + (u : ZMod n) = i + 0 := by rw [add_zero]; exact h.symm
        exact add_left_cancel h'
      exact u.ne_zero this
    · have : i + (u : ZMod n) - i = u := by ring
      rw [this]
      exact u.isUnit
  · intro a _ b _ hab
    exact Units.ext (add_left_cancel hab)
  · intro j hj
    obtain ⟨_, hu⟩ := (unitaryCayley_adj n _ _).mp (mem_filter.mp hj).2
    refine ⟨hu.unit, mem_univ _, ?_⟩
    rw [IsUnit.unit_spec]
    ring
  · intro u _
    rfl

/-- The character `χ_k(x) = e(kx/n)`. -/
noncomputable def chi (k : ZMod n) : ZMod n → ℂ := fun x => ZMod.stdAddChar (k * x)

/-- Characters are eigenvectors of the adjacency operator, with eigenvalue the Ramanujan sum. -/
theorem adj_chi (k i : ZMod n) : adj n (chi n k) i = ramanujan n k * chi n k i := by
  unfold adj chi ramanujan
  rw [sum_mul]
  refine sum_congr rfl fun u _ => ?_
  rw [mul_add, AddChar.map_add_eq_mul, mul_comm]

/-- The Laplacian eigenvalue of `X_n` attached to `χ_k`:  `λ(k) = φ(n) (1 - r(ord k))`. -/
noncomputable def lapEig (k : ZMod n) : ℝ := (Nat.totient n : ℝ) * (1 - r (addOrderOf k))

/-- **Spectrum of `X_n`** (equation (2.4)): `L χ_k = φ(n)(1 - μ(M)/φ(M)) χ_k`, `M = ord k`. -/
theorem lap_chi (k i : ZMod n) : lap n (chi n k) i = ((lapEig n k : ℝ) : ℂ) * chi n k i := by
  unfold lap lapEig
  rw [adj_chi, ramanujan_eq]
  push_cast
  ring

variable {n}

theorem one_lt_addOrderOf {k : ZMod n} (hk : k ≠ 0) : 1 < addOrderOf k := by
  have h1 : addOrderOf k ≠ 1 := fun h => hk (AddMonoid.addOrderOf_eq_one_iff.mp h)
  have h0 : 0 < addOrderOf k := addOrderOf_pos k
  omega

theorem addOrderOf_dvd_self (k : ZMod n) : addOrderOf k ∣ n := by
  have := addOrderOf_dvd_card (x := k)
  rwa [ZMod.card] at this

/-- For `M ∣ n`, the residue `n / M` has additive order `M`. -/
theorem addOrderOf_natCast_div {M : ℕ} (hM : M ∣ n) :
    addOrderOf ((n / M : ℕ) : ZMod n) = M := by
  have hn0 : n ≠ 0 := NeZero.ne n
  rw [ZMod.addOrderOf_coe _ hn0, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hM),
    Nat.div_div_self hM hn0]

theorem natCast_div_ne_zero {M : ℕ} (hM : M ∣ n) (h1 : 1 < M) : ((n / M : ℕ) : ZMod n) ≠ 0 := by
  intro h
  have := addOrderOf_natCast_div (n := n) hM
  rw [h, addOrderOf_zero] at this
  omega

/-! ### Theorem 3.2: the extreme Laplacian eigenvalues -/

/-- **Theorem 3.2, upper bound.**  Every eigenvalue is at most `φ(n) p/(p-1)`, `p = minFac n`. -/
theorem lapEig_le (k : ZMod n) (hk : k ≠ 0) :
    lapEig n k ≤ (Nat.totient n : ℝ) * ((n.minFac : ℝ) / ((n.minFac : ℝ) - 1)) := by
  have h := r_ge_of_dvd (one_lt_addOrderOf hk) (addOrderOf_dvd_self k)
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hk (Subsingleton.elim _ _)
  have hp : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast (Nat.minFac_prime hn1).two_le
  have hp1 : (0 : ℝ) < (n.minFac : ℝ) - 1 := by linarith
  have hφ : (0 : ℝ) ≤ (Nat.totient n : ℝ) := Nat.cast_nonneg _
  have e : (n.minFac : ℝ) / ((n.minFac : ℝ) - 1) = 1 - (-1 / ((n.minFac : ℝ) - 1)) := by
    field_simp
    ring
  unfold lapEig
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) hφ

/-- **Theorem 3.2, `λ_max` is attained** at the residue `n / p`. -/
theorem lapEig_minFac (hn : 1 < n) :
    lapEig n ((n / n.minFac : ℕ) : ZMod n)
      = (Nat.totient n : ℝ) * ((n.minFac : ℝ) / ((n.minFac : ℝ) - 1)) := by
  have hn1 : n ≠ 1 := by omega
  have hp : (2 : ℝ) ≤ (n.minFac : ℝ) := by exact_mod_cast (Nat.minFac_prime hn1).two_le
  have hp1 : (n.minFac : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (n.minFac : ℝ) - 1 := by linarith
    exact this.ne'
  unfold lapEig
  rw [addOrderOf_natCast_div (Nat.minFac_dvd n), r_minFac hn1]
  field_simp
  ring

/-- **Theorem 3.2, lower bound when `ω(n) ≥ 2`.**  Here `p < q` are the two smallest prime
divisors of `n`. -/
theorem lapEig_ge_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hprimes : ∀ l : ℕ, l.Prime → l ∣ n → l = p ∨ q ≤ l) (k : ZMod n) (hk : k ≠ 0) :
    (Nat.totient n : ℝ) * (1 - 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1))) ≤ lapEig n k := by
  have h := r_le_of_dvd hp hq hpq hprimes (one_lt_addOrderOf hk) (addOrderOf_dvd_self k)
  have hφ : (0 : ℝ) ≤ (Nat.totient n : ℝ) := Nat.cast_nonneg _
  unfold lapEig
  exact mul_le_mul_of_nonneg_left (by linarith) hφ

/-- **Theorem 3.2, `λ₂` is attained** at the residue `n / (pq)` when `pq ∣ n`. -/
theorem lapEig_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hdvd : p * q ∣ n) :
    lapEig n ((n / (p * q) : ℕ) : ZMod n)
      = (Nat.totient n : ℝ) * (1 - 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1))) := by
  unfold lapEig
  rw [addOrderOf_natCast_div hdvd, r_mul_primes hp hq hpq]

/-- **Theorem 3.2, lower bound for prime powers.** -/
theorem lapEig_ge_prime_pow {p a : ℕ} (hp : p.Prime) (hn : n = p ^ a) (k : ZMod n) (hk : k ≠ 0) :
    (Nat.totient n : ℝ) ≤ lapEig n k := by
  have hd : addOrderOf k ∣ p ^ a := hn ▸ addOrderOf_dvd_self k
  have h := r_le_zero_of_dvd_prime_pow hp (one_lt_addOrderOf hk) hd
  have hφ : (0 : ℝ) ≤ (Nat.totient n : ℝ) := Nat.cast_nonneg _
  unfold lapEig
  nlinarith [mul_nonneg hφ (neg_nonneg.mpr h)]

/-- **Theorem 3.2, `λ₂ = φ(n)` is attained for `n = p^a`, `a ≥ 2`,** at the residue `n / p²`. -/
theorem lapEig_prime_sq {p : ℕ} (hp : p.Prime) (hdvd : p ^ 2 ∣ n) :
    lapEig n ((n / p ^ 2 : ℕ) : ZMod n) = (Nat.totient n : ℝ) := by
  unfold lapEig
  rw [addOrderOf_natCast_div hdvd, r_prime_sq hp]
  ring

/-! ### Theorem 4.3: the exact consensus rate on `X_n` -/

omit [NeZero n] in
/-- **Theorem 4.3 for `X_n`, `ω(n) ≥ 2`.**  With `λ₂` and `λ_max` the extreme Laplacian
eigenvalues from Theorem 3.2, the optimal rate `(λ_max - λ₂)/(λ_max + λ₂)` equals
`q / (2(p-1)(q-1) + q - 2)`. -/
theorem consensus_rate_unitaryCayley {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpn : n.minFac = p) :
    let l2 := (Nat.totient n : ℝ) * (1 - 1 / (((p : ℝ) - 1) * ((q : ℝ) - 1)))
    let lmax := (Nat.totient n : ℝ) * ((n.minFac : ℝ) / ((n.minFac : ℝ) - 1))
    (lmax - l2) * (2 * ((p : ℝ) - 1) * ((q : ℝ) - 1) + (q : ℝ) - 2) = (q : ℝ) * (lmax + l2) := by
  intro l2 lmax
  have hp2 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hq2 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq.one_lt
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    exact this.ne'
  have hq1 : (q : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) - 1 := by linarith
    exact this.ne'
  refine rate_two_primes (φ := (Nat.totient n : ℝ)) hp2 hq2 ?_ ?_
  · simp only [l2]
    field_simp
  · simp only [lmax, hpn]
    field_simp

end ArithmeticDynamics
