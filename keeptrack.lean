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

lemma TisNotPathConnSup : ¬ (IsPathConnected T)  := by

  intro hPathConn
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

  let xcoor : ℝ × ℝ → ℝ := Prod.fst
  have xcoorContinuous:  Continuous (xcoor : ℝ × ℝ → ℝ) :=
    continuous_fst

  apply IsPathConnected.joinedIn at hPathConn
  specialize hPathConn z hz w hw
  let hPath := JoinedIn.somePath hPathConn

  let xcoordPath := fun t => xcoor (hPath t)
  have xcoordPathContinuous : Continuous (xcoordPath : unitInterval → ℝ) := by
    apply xcoorContinuous.comp
    · exact hPath.continuous

  let A : Set unitInterval := { t | xcoordPath t = 0 }

  have A_closed : IsClosed A := by
    exact isClosed_singleton.preimage xcoordPathContinuous

  have A_nonempty : A.Nonempty := by
    use 0
    have h_xcoordPath0 : xcoordPath 0 = 0 := by
      simp only [xcoordPath, Function.comp_apply, xcoor]
      rw [hPath.source]

    exact h_xcoordPath0


  have A_compact : IsCompact A := by
    exact A_closed.isCompact

  let t₀ : unitInterval := sSup A

  have t₀_mem : t₀ ∈ A :=
    IsCompact.sSup_mem A_compact A_nonempty

  have xcoordPathAtTEqZero : xcoordPath t₀ = 0 :=
    t₀_mem
  -- , so p(t0) = (0, 0)
  -- I don't ike this too long
  have hPathT₀: hPath t₀ = z := by
    unfold z
    apply Prod.ext_iff.mpr

    have hPathT₀IsInT : hPath t₀ ∈ T := by
      exact hPathConn.somePath_mem t₀

    have hPathT₀_x_is_0 : (hPath t₀).1 = 0 := by
      exact xcoordPathAtTEqZero

    unfold T at hPathT₀IsInT

    constructor
    · apply xcoordPathAtTEqZero
    ·cases hPathT₀IsInT with
    | inl hS =>
        exfalso

        obtain ⟨xPosreal, hxInPosReal, h_eq_path⟩ := hS
        let x_val : ℝ := xPosreal
        have hx_valPos : x_val > 0 := by
         dsimp [x_val] at *
         dsimp [PosReal] at hxInPosReal
         simpa using hxInPosReal

        have hPath_x_eq_x_val : (hPath t₀).1 = x_val := by
          simpa [sinCurve, x_val] using
          (congrArg Prod.fst h_eq_path).symm


        rw [hPath_x_eq_x_val] at hPathT₀_x_is_0
        linarith [hx_valPos, hPathT₀_x_is_0]

    | inr hZ =>

        have hZ_eq : hPath t₀ = (0, 0) := by
          simpa [Z] using hZ

        have hPathT₀_y_is_0 : (hPath t₀).2 = 0 := by
          simpa using congrArg Prod.snd hZ_eq

        exact hPathT₀_y_is_0

  have epsDeltaBoundAtT₀ : ∃ δ > 0, ∀ t : unitInterval, dist t t₀ < δ →
    dist (hPath t) (hPath t₀) < 1/2 := by
    have hTendstoEventually := Metric.tendsto_nhds.mp (hPath.continuousAt t₀)
    have hEventually : ∀ᶠ (t : unitInterval) in 𝓝 t₀, dist (hPath t) (hPath t₀) < 1/2 := by
      specialize hTendstoEventually (1/2)
      apply hTendstoEventually
      norm_num
    exact Metric.eventually_nhds_iff.mp hEventually

  obtain ⟨δ , hδ, ht⟩ := epsDeltaBoundAtT₀
   -- let t₁ in the reange of
   -- create a real that is in unitinterval and then used (since unitinvterval doen ahave )

  have t₁Let₀ : ∃ t₁:unitInterval, t₁ > t₀  ∧ dist t₁ t₀ < δ := by
    let s0 := (t₀ : ℝ)
    let s1 := min (s0 + δ/2) 1
    have h : 0 ≤ s1 := sorry
    have h': s1 ≤ 1 := sorry
    use ⟨s1, h, h'⟩
    constructor
    · simp only [gt_iff_lt, ← Subtype.coe_lt_coe, Subtype.coe_mk]
      sorry
    · sorry
  -- have t₁Get₀ : ∃ t₁:unitInterval, t₁ > t₀  ∧ dist t₁ t₀ < δ := by
  --   have t₀DeltainUnitinterval
  --   use (((t₀ : ℝ) + (δ/2)) : unitInterval) -- not sure
  --   sorry

  obtain ⟨t₁, ht₁⟩ := t₁Let₀
  -- PROOF:  such that a := x(p(t1)) > 0
  let a :=  xcoordPath t₁
  have aGr0  : a > 0 := by sorry

  -- PROOF: The image x(p([t0, t1])) is connected
  let intervalT₀T₁ := Set.Icc t₁ t₀

  have xcoordPathOfT₀T₁Conn:
      IsConnected ( xcoordPath '' intervalT₀T₁) := by
    have hConn : IsConnected intervalT₀T₁ := by
      unfold intervalT₀T₁
      sorry
    have hCont : ContinuousOn xcoordPath intervalT₀T₁ := by sorry

    exact hConn.image _ hCont


  -- PROOF: and contains 0 = x(p(t₀)) and a = x(p(t₁))
  let zero :=  xcoordPath t₀

  have leftEnd :
      zero ∈ ( xcoordPath '' intervalT₀T₁) := by sorry

  have rightEnd :
      a ∈ ( xcoordPath '' intervalT₀T₁) := by sorry

  -- PROOF: and every connected subset of R is an interval, so
  -- (3.3) [0, a] ⊂ x(p([t0, t1])).
  let intervalAZero := Set.Icc a zero
  have intervalAZeroIn : intervalAZero ⊆ (xcoordPath '' intervalT₀T₁) := by sorry


  -- PROOF: This contradicts continuity of t 7→ x(p(t)) at t0 by the picture above, because the graph of
  -- sin(1/x) is oscillating in and out of the red circle, so the x-values on S inside the circle do
  -- not contain a whole interval like [0, a]. To turn this visual idea into a strict logical argument
  -- we look at where the peaks and troughs occur in S.

-- PROOF: Since sin(θ) = 1 if and only if θ = (4k + 1) π/2
-- and sin(θ) = −1 if and only if θ = (4k −1)π/2,where k ∈ Z,
-- we have (x,sin(1/x)) = (x, 1)
-- if x = 2/((4k + 1)π)
-- and (x,sin(1/x)) = (x, −1) if x = 2/((4k − 1)π) for k ∈ Z.
-- not necessarily -1

-- PROOF: Such x-values get arbitrarily close to 0 for large k,


-- PROOF:so there are such x-values of both kinds in [0, a].

-- PROOF:Therefore by (3.3) we get p(t0) = (∗, 1) and
-- PROOF:T p(t00) = (∗, −1) for some t0 and t00 in [t0, t1] ⊂ [t0, t0 + δ).

-- PROOF:TBut ||p(t0)|| = ||(∗, 1)|| > 1/2 and
-- ||p(t00)|| = ||(∗, −1)|| > 1/2, which both contradict (3.2).

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

