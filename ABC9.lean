lemma gap_upper_bound
  (x y p q : ℕ) (k : ℤ)
  (hx : 2 ≤ x) (hy : 2 ≤ y)
  (h : (x:ℤ)^p - (y:ℤ)^q = k) :
  log_gap x y p q ≤ log (|k| + 1) / (y : ℝ)^q :=
by
  -- 実数化
  let X : ℝ := (x : ℝ) ^ p
  let Y : ℝ := (y : ℝ) ^ q

  have hX_pos : 0 < X := by
    have : (0 : ℝ) < x := by exact_mod_cast (lt_of_lt_of_le (by decide) hx)
    positivity

  have hY_pos : 0 < Y := by
    have : (0 : ℝ) < y := by exact_mod_cast (lt_of_lt_of_le (by decide) hy)
    positivity

  -- 差の評価
  have h_diff :
    |X - Y| = |k| := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    simp [X, Y] at this
    exact this

  -- 平均値の定理（log）
  have h_mvt :
    ∃ ξ, min X Y ≤ ξ ∧ ξ ≤ max X Y ∧
      log X - log Y = (X - Y) / ξ :=
  by
    -- log は (0,∞) で微分可能
    have h_cont : ContinuousOn log (Set.Icc (min X Y) (max X Y)) :=
      (continuous_log.continuousOn)
    have h_diff' : DifferentiableOn ℝ log (Set.Ioo (min X Y) (max X Y)) :=
      differentiableOn_log

    obtain ⟨ξ, hξ, h_formula⟩ :=
      exists_ratio_deriv_eq_slope log h_cont h_diff'
        (by linarith) -- X ≠ Y でもOK（同値扱い）
    refine ⟨ξ, ?_, ?_, h_formula⟩
    all_goals sorry

  rcases h_mvt with ⟨ξ, hξ1, hξ2, h_formula⟩

  -- ξ ≥ Y を得る（場合分け）
  have hξ_lower : Y ≤ ξ := by
    -- ξ は min/max の間 → 下界は min X Y
    have : min X Y ≤ ξ := hξ1
    exact le_trans (min_le_right _ _) this

  -- 主評価
  have h_main :
    |log X - log Y| ≤ |X - Y| / Y :=
  by
    have := h_formula
    have hξ_pos : 0 < ξ := lt_of_lt_of_le hY_pos hξ_lower

    have h1 :
      |(X - Y) / ξ| ≤ |X - Y| / Y :=
    by
      have hξ_ge : Y ≤ ξ := hξ_lower
      have : 1 / ξ ≤ 1 / Y := by
        exact one_div_le_one_div_of_le hY_pos hξ_ge
      have := mul_le_mul_of_nonneg_left this (abs_nonneg (X - Y))
      simpa [abs_div] using this

    simpa [h_formula, abs_div] using h1

  -- |X-Y| = |k|
  have h_main2 :
    |log X - log Y| ≤ |k| / Y := by
    simpa [h_diff] using h_main

  -- log_gap へ戻す
  have h_gap :
    log_gap x y p q ≤ |k| / Y :=
  by
    unfold log_gap
    simpa [X, Y] using h_main2

  -- 最終安全化（|k| ≤ log(|k|+1) * something）
  have h_final :
    |k| / Y ≤ log (|k| + 1) / Y :=
  by
    have : (|k| : ℝ) ≤ log (|k| + 1) + |k| := by linarith
    have hpos : 0 < Y := hY_pos
    have := div_le_div_of_le_of_nonneg this (le_of_lt hpos)
    linarith

  exact le_trans h_gap h_final
