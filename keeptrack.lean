import Mathlib

open Topology Filter

def PosReal := Set.Ioi (0 : ℝ)
noncomputable def sinCurve := fun x ↦ (x, Real.sin (x⁻¹))

def S : Set (ℝ × ℝ) := (sinCurve) '' PosReal

def Z : Set (ℝ × ℝ) := { (0, 0) }

def T : Set (ℝ × ℝ) := S ∪ Z

-- T is Not Path-connected

local instance : Fact ((0 : ℝ) ≤ 1) := ⟨by linarith⟩
noncomputable instance : CompleteLattice unitInterval := by infer_instance


lemma TisNotPathConn : ¬ (IsPathConnected T)  := by

  -- Suppose there exists a path
  intro hPathConn

  -- Pick two points in T: the limit point of S (0,0) and some point  (x > 0, y= sin(1⧸x) )
  let z : ℝ×ℝ := (0, 0)
  let w_x: ℝ := (2)⁻¹
  let w : ℝ×ℝ := sinCurve w_x
  have hz : z ∈ T := by
    right
    simp [Z]
    rfl
  have hw : w ∈ T := by
    rw [T,S]
    left
    simp only [Set.mem_image]
    use w_x
    constructor
    · unfold PosReal Set.Ioi
      norm_num
    · rfl

  -- Let x: R^2 → R be the x-coordinate function, which is continuous
  let xcoor : ℝ × ℝ → ℝ := Prod.fst
  have xcoorContinuous:  Continuous (xcoor : ℝ × ℝ → ℝ) :=
    continuous_fst

  -- Let p be  a Path from z to w in T
  apply IsPathConnected.joinedIn at hPathConn
  specialize hPathConn z hz w hw
  have hPath := JoinedIn.somePath hPathConn

  let xcoordPath := fun t => xcoor (hPath t)
  have xcoordPathContinuous : Continuous (xcoordPath : unitInterval → ℝ) := by
    apply xcoorContinuous.comp
    · exact hPath.continuous

  -- Let t0 = inf{t ∈ [0, 1] : x(p(t)) > 0} (times of jump from z to sine curve)
  -- let A : Set unitInterval := { t |xcoordPath t > 0 }
  -- let t₀ := sInf A

  let A : Set unitInterval := { t | xcoordPath t = 0 }
  let t₀ := sSup A

  -- For t > t0, x(p(t)) > 0
  have hLet₀ : ∀ t : unitInterval, t > t₀ → xcoordPath t = 0 := by sorry


  -- By continuity of x ◦ p at t0, x(p(t0)) = limt→t_0 x(p(t)) = 0, so p(t0) = (0, 0).

    -- x(p(t0)) = limt→t₀⊹ x(p(t)) = 0 ( use closness of set A )
  have left_limit : Tendsto xcoordPath (𝓝[>] t₀) (𝓝 0)  := by
    -- apply tendsto_nhds_unique (ContinuousAt.tendsto (xcoordPathContinuous.continuousAt t₀)) (tendsto_const_nhds 0)
    -- exact nhds_ne_bot 0
    sorry
  have hRightLimEq : xcoordPath t₀ = 0 := by
    -- rw ← tendsto_nhds_unique (xcoordPathContinuous.continuousAt t₀) left_limit
    sorry
    -- sorry

  -- 0, so p(t0) = (0, 0)
  have hPathT₀: hPath t₀ = z := by sorry

  -- By continuity of p at t₀, there is δ > 0 such that
  -- ∀ t ∈ [t₀, t₀+δ], ||p(t) - p(t₀)|| < 1/2

  have continuityBound : ∃ δ > 0, ∀ t : unitInterval, dist t t₀ < δ →
    dist (hPath t) (hPath t₀) < 1/2 := by
    -- Start with the Tendsto statement from continuity
    have h_tendsto := hPath.continuousAt t₀
    -- Convert to the "forall epsilon eventually" form
    have h_tendsto_eventually := Metric.tendsto_nhds.mp h_tendsto
    -- Specialize for epsilon = 1/2
    have h_eventually : ∀ᶠ (t : unitInterval) in 𝓝 t₀, dist (hPath t) (hPath t₀) < 1/2 := by
      specialize h_tendsto_eventually (1/2)
      apply h_tendsto_eventually
      norm_num -- Prove 1/2 > 0
    -- Convert the "eventually" form to the "exists delta" form
    exact Metric.eventually_nhds_iff.mp h_eventually

    -- (hPath.continuousAt t₀).exists_delta 1/2 (by norm_num)
    -- By the definition of t0 as an infimum, for this same δ there is a t1 with t0 < t1 < t0 + δ
  obtain ⟨δ , hδ⟩ := continuityBound
  have t₁Grt₀ : ∃ t₁:unitInterval, t₀ < t₁ ∧ dist t₁ t₀ < δ := by
   sorry
  --such that a := x(p(t1)) > 0
  sorry


-- def clsOfS := closure S

-- lemma TsubClsOfS : T ⊆ clsOfS := by
--   intro x hx
--   cases hx with
--   | inl hxS => exact subset_closure hxS
--   | inr hxZ =>
--       rw [hxZ]
--       let f :  ℕ →  ℝ × ℝ := fun n => ((n * Real.pi)⁻¹, 0)
--       have hnMulpiAtTop : Tendsto (fun n : ℕ => n* Real.pi) atTop atTop := by
--         apply Filter.Tendsto.atTop_mul_const'
--         · exact Real.pi_pos
--         · exact tendsto_natCast_atTop_atTop
--       have hf : Tendsto f atTop (𝓝 (0, 0))  := by
--         apply Filter.Tendsto.prodMk_nhds
--         · exact tendsto_inv_atTop_zero.comp hnMulpiAtTop
--         · exact tendsto_const_nhds
--       have hf' : ∀ᶠ n in atTop, f n ∈ S := by
--         have hfInS : ∀ n : ℕ, 0 < n → f n ∈ S := by
--           intro n hn
--           use (n * Real.pi)⁻¹
--           constructor
--           unfold PosReal
--           rw [Set.mem_Ioi]
--           · apply inv_pos.mpr
--             apply mul_pos
--             · exact Nat.cast_pos.mpr hn
--             · exact Real.pi_pos
--           · unfold f
--             calc sinCurve (n * Real.pi)⁻¹ =
--               ((n * Real.pi)⁻¹, Real.sin ((n * Real.pi)⁻¹)⁻¹) := by rfl
--               _ = ((n * Real.pi)⁻¹, Real.sin (n * Real.pi)) := by
--                   congr
--                   simp only [inv_inv]
--               _ = ((n * Real.pi)⁻¹,0) := by
--                 congr
--                 apply Real.sin_nat_mul_pi
--         filter_upwards [eventually_gt_atTop 0] using hfInS
--       apply mem_closure_of_tendsto hf hf'



-- -- SineCurve is continuous and path-connected
-- lemma invFunIsContinuousOnPosReal : ContinuousOn (fun x : ℝ => x⁻¹) (PosReal) := by
--   apply ContinuousOn.inv₀
--   · exact continuous_id.continuousOn
--   · intro x hxIsInIoi
--     exact ne_of_gt hxIsInIoi

-- lemma sinWithinvFunIsContinuousOnPosReal : ContinuousOn (fun x : ℝ => Real.sin (x⁻¹)) (PosReal) := by
--   apply Real.continuous_sin.comp_continuousOn
--   · exact invFunIsContinuousOnPosReal

-- lemma topoSinCurveIsContinuousOnPosReal : ContinuousOn (sinCurve) (PosReal) :=
--   ContinuousOn.prod_mk continuous_id.continuousOn sinWithinvFunIsContinuousOnPosReal

-- lemma posIntervalIsPathConnected : IsPathConnected (PosReal) := by
--   apply Convex.isPathConnected
--   · exact convex_Ioi 0
--   · use 1
--     unfold PosReal
--     simp

-- lemma SIsPathConn : IsPathConnected S := by
--   apply IsPathConnected.image'
--   · exact posIntervalIsPathConnected
--   · exact topoSinCurveIsContinuousOnPosReal

-- lemma SisConnected : IsConnected S := SIsPathConn.isConnected

-- lemma ZisConnected : IsConnected Z := isConnected_singleton

-- -- T is connected

-- theorem TisConnected : IsConnected T := by
--   apply IsConnected.subset_closure
--   · exact SisConnected
--   · tauto_set
--   · exact TsubClsOfS
