/-
Arithmetic Dynamics on Unitary Cayley and GCD Graphs
Part III: totient bounds behind the extremal Ramanujan sums (Section 3 of the paper).
-/
import Mathlib

namespace ArithmeticDynamics

/-- If a prime `p` divides `M > 0`, then `p - 1 ≤ φ(M)`. -/
theorem pred_prime_le_totient {p M : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hM : 0 < M) :
    p - 1 ≤ Nat.totient M := by
  have h : Nat.totient p ∣ Nat.totient M := Nat.totient_dvd_of_dvd hpM
  rw [Nat.totient_prime hp] at h
  exact Nat.le_of_dvd (Nat.totient_pos.mpr hM) h

/-- **Lemma 3.1 (i), totient form.**  If `1 < M` and `M ∣ n`, then
`minFac n - 1 ≤ φ(M)`; consequently `-1/φ(M) ≥ -1/(minFac n - 1)`. -/
theorem minFac_pred_le_totient {n M : ℕ} (hM : 1 < M) (hMn : M ∣ n) :
    n.minFac - 1 ≤ Nat.totient M := by
  have hprime : M.minFac.Prime := Nat.minFac_prime (by omega)
  have hdvd : M.minFac ∣ n := dvd_trans (Nat.minFac_dvd M) hMn
  have h1 : n.minFac ≤ M.minFac := Nat.minFac_le_of_dvd hprime.two_le hdvd
  have h2 : M.minFac - 1 ≤ Nat.totient M :=
    pred_prime_le_totient hprime (Nat.minFac_dvd M) (by omega)
  omega

end ArithmeticDynamics
