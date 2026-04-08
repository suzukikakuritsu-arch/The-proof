lemma gap_upper_bound
  (x y p q : ℕ) (k : ℤ)
  (hx : 2 ≤ x) (hy : 2 ≤ y)
  (h : (x:ℤ)^p - (y:ℤ)^q = k) :
  log_gap x y p q ≤ (|k| : ℝ) / (y : ℝ)^q :=
by
  let X : ℝ := (x : ℝ) ^ p
  let Y : ℝ := (y : ℝ) ^ q

  have hX_pos : 0 < X := by
    have : (0 : ℝ) < x := by exact_mod_cast (lt_of_lt_of_le (by decide) hx)
    positivity

  have hY_pos : 0 < Y := by
    have : (0 : ℝ) < y := by exact_mod_cast (lt_of_lt_of_le (by decide) hy)
    positivity

  have h_diff :
    |X - Y| = |k| := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    simpa [X, Y] using this

  -- 平均値の定理
  have h_mvt :
    ∃ ξ, ξ ∈ Set.Ioo (min X Y) (max X Y) ∧
      log X - log Y = (X - Y) / ξ :=
  by
    have h_cont : ContinuousOn log (Set.Icc (min X Y) (max X Y)) :=
      continuous_log.continuousOn
    have h_diff' :
      DifferentiableOn ℝ log (Set.Ioo (min X Y) (max X Y)) :=
      differentiableOn_log

    exact exists_ratio_deriv_eq_slope log h_cont h_diff' (by linarith)

  rcases h_mvt with ⟨ξ, hξ, h_formula⟩

  -- ξ ≥ Y
  have hξ_lower : Y ≤ ξ := by
    have : min X Y ≤ ξ := (Set.Ioo_subset_Icc_self hξ).1
    exact le_trans (min_le_right _ _) this

  have h_main :
    |log X - log Y| ≤ |X - Y| / Y :=
  by
    have hξ_pos : 0 < ξ := lt_trans hY_pos hξ_lower

    have h_inv : (1 / ξ) ≤ (1 / Y) :=
      one_div_le_one_div_of_le hY_pos hξ_lower

    have := mul_le_mul_of_nonneg_left h_inv (abs_nonneg (X - Y))
    simpa [abs_div] using this

  have :
    |log X - log Y| ≤ (|k| : ℝ) / Y :=
  by
    simpa [h_diff] using h_main

  unfold log_gap
  simpa [X, Y] using this
