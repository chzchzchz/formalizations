import McCulloch26_2.MultiPrime
import McCulloch26_2.PropClass
import McCulloch26_2.Basic

namespace McCulloch26_2

open scoped Nat

variable {N : ℕ}

theorem two_odd_components_imp_four_dvd_num
    (pp : Fin N → ℕ) (nn : Fin N → ℕ) (ff : ∀ i, Fin (nn i) → ℕ)
    (hpp : ∀ i, (pp i).Prime) (hs : ∀ i, Sorted (ff i)) (hpos : ∀ i, Pos (ff i))
    (hN : ∀ i, 0 < nn i)
    {i j : Fin N}
    (hodd_i : Odd (pp i)) (hodd_j : Odd (pp j)) :
    4 ∣ (autRatio (pp i) (ff i)).num * (autRatio (pp j) (ff j)).num := by
  let pi := pp i
  let pj := pp j
  let fi := ff i
  let fj := ff j
  have hpi : pi.Prime := hpp i
  have hpj : pj.Prime := hpp j
  have hsi : Sorted fi := hs i
  have hsj : Sorted fj := hs j
  have hposi : Pos fi := hpos i
  have hposj : Pos fj := hpos j
  have hni : 0 < nn i := hN i
  have hnj : 0 < nn j := hN j
  -- numerator divisible by p-1
  have hdvi : ((pi - 1 : ℕ) : ℤ) ∣ (autRatio pi fi).num :=
    num_autRatio_dvd_pm1 hpi hsi hposi hni
  have hdissue : ((pj - 1 : ℕ) : ℤ) ∣ (autRatio pj fj).num :=
    num_autRatio_dvd_pm1 hpj hsj hposj hnj
  -- for odd prime, p-1 is even
  rcases hodd_i with ⟨ki, hki⟩
  rcases hodd_j with ⟨kj, hkj⟩
  have hpi_eq : pi = 2 * ki + 1 := by unfold pi; exact hki
  have hpj_eq : pj = 2 * kj + 1 := by unfold pj; exact hkj
  have hevi : 2 ∣ pi - 1 := by
    rw [hpi_eq]
    exact ⟨ki, by simp⟩
  have hevj : 2 ∣ pj - 1 := by
    rw [hpj_eq]
    exact ⟨kj, by simp⟩
  -- lift divisibility to ℤ
  have h2i : (2 : ℤ) ∣ (autRatio pi fi).num := by
    have : (2 : ℤ) ∣ ((pi - 1 : ℕ) : ℤ) := by exact_mod_cast hevi
    exact Int.dvd_trans this hdvi
  have h2j : (2 : ℤ) ∣ (autRatio pj fj).num := by
    have : (2 : ℤ) ∣ ((pj - 1 : ℕ) : ℤ) := by exact_mod_cast hevj
    exact Int.dvd_trans this hdissue
  -- product divisible by 4
  have h4 : (4 : ℤ) ∣ (autRatio pi fi).num * (autRatio pj fj).num := by
    have h1 : (2 : ℤ) * 2 ∣ (autRatio pi fi).num * (autRatio pj fj).num := by
      have := Int.mul_dvd_mul h2i h2j
      simpa [Int.mul_comm] using this
    rw [show (2 : ℤ) * 2 = 4 by norm_num] at h1
    exact h1
  exact_mod_cast h4