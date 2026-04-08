  -- Step 0: 前提
  obtain ⟨C, A, hC, hA, h_low⟩ :=
    baker_lower_bound x y p q

  have h_up :=
    gap_upper_bound x y p q k h_eq

  have h_comb :
    C * ((q : ℝ) * log y)^(-A)
      ≤ (|k| : ℝ) / (y : ℝ)^q := by
    exact le_trans h_low h_up

  have hy_real : 1 < (y : ℝ) := by exact_mod_cast hy
  have hlogy_pos : 0 < log (y : ℝ) := log_pos hy_real

  -- ============================================================
  -- STEP 1: 形の正規化（y^q ≤ Const * q^A）
  -- ============================================================

  have h_bound :
    (y : ℝ)^q ≤ (|k| / C) * ((q : ℝ) * log y)^A := by
  {
    have h_pos : 0 < (y : ℝ)^q := by positivity

    -- 両辺に (y^q) を掛ける
    have h1 :=
      mul_le_mul_of_nonneg_right h_comb (le_of_lt h_pos)

    -- 整形
    have h2 :
      C * ((q : ℝ) * log y)^(-A) * (y : ℝ)^q ≤ |k| := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h1

    -- 逆数を使って移項
    have hCpos : 0 < C := hC
    have h3 :
      (y : ℝ)^q ≤ (|k| / C) * ((q : ℝ) * log y)^A := by
    {
      have :=
        (le_div_iff₀ hCpos).mpr ?_
      · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
      ·
        -- 右辺の整形
        have :
          C * ((q : ℝ) * log y)^(-A) * (y : ℝ)^q ≤ |k| := h2
        simpa [rpow_neg, inv_pow, inv_mul_eq_iff_eq_mul₀] using this
    }
    exact h3
  }

  -- log y を分離（定数化）
  have h_bound' :
    (y : ℝ)^q ≤ (|k| / C) * (log y)^A * (q : ℝ)^A := by
  {
    have :
      ((q : ℝ) * log y)^A = (q : ℝ)^A * (log y)^A := by
      simpa using (mul_rpow (by positivity) (le_of_lt hlogy_pos) A)

    simpa [this, mul_comm, mul_left_comm, mul_assoc] using h_bound
  }

  -- ============================================================
  -- STEP 2: 定数吸収（A+1 を使う）
  -- ============================================================

  set K0 : ℝ := (|k| / C) * (log y)^A

  have h_bound'' :
    (y : ℝ)^q ≤ K0 * (q : ℝ)^A := by
    simpa [K0] using h_bound'

  -- 指数優越（A+1）
  obtain ⟨N, hN⟩ :=
    exp_dominates_poly (y : ℝ) hy_real (A + 1) (by linarith)

  -- 定数吸収用の閾値
  let N' : ℕ := max N (Nat.ceil K0)

  have hqN : q ≥ N' := by
    exact le_trans (le_max_left _ _) hq_large

  have h_exp :
    (y : ℝ)^q > (q : ℝ)^(A + 1) :=
    hN q (le_trans (le_max_left _ _) hqN)

  -- q ≥ K0 を保証
  have hqK : (q : ℝ) ≥ K0 := by
  {
    have : (q : ℝ) ≥ (Nat.ceil K0 : ℝ) :=
      by exact_mod_cast (le_trans (le_max_right _ _) hqN)
    exact le_trans this (Nat.le_ceil _)
  }

  -- q^(A+1) ≥ K0 * q^A
  have h_poly :
    (q : ℝ)^(A + 1) ≥ K0 * (q : ℝ)^A := by
  {
    have hq_pos : 0 ≤ (q : ℝ)^A := by positivity
    have :=
      mul_le_mul_of_nonneg_right hqK hq_pos
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
  }

  -- ============================================================
  -- STEP 3: 矛盾
  -- ============================================================

  have h_final :
    (y : ℝ)^q > K0 * (q : ℝ)^A :=
    lt_of_lt_of_le h_exp h_poly

  have := lt_of_le_of_lt h_bound'' h_final

  exact lt_irrefl _ this
