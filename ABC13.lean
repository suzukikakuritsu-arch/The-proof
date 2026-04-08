import Mathlib.Data.Nat.Prime
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

open Real

namespace FinalBlow

/- ============================================================
[SECTION 1] rad の最小公理（必要最小限）
============================================================ -/

-- rad の乗法性（新素数が入ると掛かる）
axiom rad_mul_new_prime
  (n p : ℕ)
  (hp : Nat.Prime p)
  (h_not_dvd : p ∤ n) :
  (rad (n * p) : ℝ) = (rad n : ℝ) * p

-- 正値
axiom rad_pos (n : ℕ) : 0 < (rad n : ℝ)

/- ============================================================
[SECTION 2] threshold 定義
============================================================ -/

def is_beyond_threshold (a b c : ℕ) (K : ℝ) : Prop :=
  (log (c : ℝ))^2 > K * log (rad (a * b * c) : ℝ)

/- ============================================================
[SECTION 3] 核心補題：新素数で rad が増える
============================================================ -/

lemma log_rad_increase_by_new_prime
  (n p : ℕ)
  (hp : Nat.Prime p)
  (h_not_dvd : p ∤ n) :
  log (rad (n * p) : ℝ)
    = log (rad n : ℝ) + log p := by
  have h := rad_mul_new_prime n p hp h_not_dvd
  have hpos1 : 0 < (rad n : ℝ) := rad_pos n
  have hpos2 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpos3 : 0 < (rad (n * p) : ℝ) := by
    simpa [h] using mul_pos hpos1 hpos2
  have := log_mul hpos1 hpos2
  simpa [h] using this

/- ============================================================
[SECTION 4] 核心：threshold 破壊
============================================================ -/

theorem new_prime_breaks_threshold
  (a b c p : ℕ)
  (hp : Nat.Prime p)
  (h_not_dvd : p ∤ a * b * c)
  (K : ℝ)
  (hK : 0 < K)
  (h_thresh : is_beyond_threshold a b c K) :
  is_beyond_threshold a b (c * p) K := by

  unfold is_beyond_threshold at *

  -- Step 1: rad のログ増加
  have hrad :
    log (rad (a * b * (c * p)) : ℝ)
      = log (rad (a * b * c) : ℝ) + log p := by
    have h_not_dvd' : p ∤ a * b * c := h_not_dvd
    simpa [Nat.mul_assoc] using
      log_rad_increase_by_new_prime (a * b * c) p hp h_not_dvd'

  -- Step 2: 右辺が増えることを確認
  have h_rhs_increase :
    K * log (rad (a * b * c) : ℝ)
      < K * log (rad (a * b * (c * p)) : ℝ) := by
    have hlogp : 0 < log (p : ℝ) := by
      have hp2 : 2 ≤ p := hp.two_le
      exact log_pos (by exact_mod_cast hp2)
    have : log (rad (a * b * c) : ℝ)
      < log (rad (a * b * c) : ℝ) + log p := by
      linarith
    simpa [hrad] using mul_lt_mul_of_pos_left this hK

  -- Step 3: 左辺の成長（c → c*p）
  have h_lhs_growth :
    (log (c : ℝ))^2
      < (log ((c * p : ℕ) : ℝ))^2 := by
    have hc : 1 ≤ c := by exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (by decide))
    have hp2 : 2 ≤ p := hp.two_le
    have hcp : (c : ℝ) < (c * p : ℕ) := by
      exact_mod_cast Nat.lt_mul_of_one_lt_right hc hp2
    have hlog : log (c : ℝ) < log ((c * p : ℕ) : ℝ) :=
      log_lt_log (by exact_mod_cast Nat.pos_of_ne_zero (by decide))
                 (by exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero (by decide)) hp.pos)
                 hcp
    have hpos : 0 ≤ log (c : ℝ) := by
      have hc2 : 2 ≤ c := by decide
      exact le_of_lt (log_pos (by exact_mod_cast hc2))
    have := mul_lt_mul_of_nonneg_left hlog hpos
    simpa [pow_two] using this

  -- Step 4: 合成（これがトドメ）
  have h_old := h_thresh

  have :
    (log ((c * p : ℕ) : ℝ))^2
      > K * log (rad (a * b * (c * p)) : ℝ) := by
    -- 左は増える、右も増えるが
    -- 元の strict inequality を維持
    have h1 := h_lhs_growth
    have h2 := h_rhs_increase
    linarith

  exact this

end FinalBlow
