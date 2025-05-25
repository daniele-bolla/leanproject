import Mathlib
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order
import Mathlib.Analysis.InnerProductSpace.PiL2

open Topology Filter Set Order

def IsInterval (s : Set ℝ) : Prop :=
  ∀ {x y : ℝ}, x ∈ s → y ∈ s → ∀ z, x ≤ z → z ≤ y → z ∈ s

def PosReal := Set.Ioi (0 : ℝ)
noncomputable def sinCurve := fun x ↦ (x, Real.sin (x⁻¹))

def S : Set (ℝ × ℝ) := (sinCurve) '' PosReal

def Z : Set (ℝ × ℝ) := { (0, 0) }

def T : Set (ℝ × ℝ) := S ∪ Z

-- T is Not Path-connected

local instance : Fact ((0 : ℝ) ≤ 1) := ⟨by linarith⟩
noncomputable instance : CompleteLattice unitInterval := by infer_instance

  def z : ℝ×ℝ := (0, 0)
  noncomputable def w_x: ℝ := (2)⁻¹
  noncomputable def w : ℝ×ℝ := sinCurve w_x
  lemma hz : z ∈ T := by
    right
    simp [Z]
    rfl
  lemma hw : w ∈ T := by
    rw [T,S]
    left
    simp only [Set.mem_image]
    use w_x
    constructor
    · unfold w_x PosReal Set.Ioi
      norm_num
    · trivial

/-- The Euclidean norm of a vector in ℝ² is greater than or equal to the absolute value of its first component -/
theorem norm_ge_abs_component_fst {a b : ℝ} : ‖(a, b)‖ ≥ |a| := by
  -- Definition of norm squared in ℝ²
  have norm_squared : ‖(a, b)‖^2 = a^2 + b^2 := by rfl

  -- Since b² ≥ 0, we have a² + b² ≥ a²
  have sum_ge_component : a^2 + b^2 ≥ a^2 := by
    apply add_le_add_left
    exact sq_nonneg b

  -- Apply square root to both sides
  have sqrt_ineq : ‖(a, b)‖ ≥ sqrt(a^2) := by
    rw [←norm_squared]
    apply Real.sqrt_le_sqrt
    · exact sum_ge_component

  -- Use sqrt(x²) = |x|
  rw [Real.sqrt_sq_eq_abs] at sqrt_ineq
  exact sqrt_ineq

/-- The Euclidean norm of a vector in ℝ² is greater than or equal to the absolute value of its second component -/
lemma norm_ge_abs_component_snd {a b : ℝ} : ‖(a, b)‖ ≥ |b| := by sorry

lemma xcoordPathContinuous (hPath : unitInterval → ℝ×ℝ) (hCont : Continuous hPath) : Continuous (fun t => (hPath t).1) :=
  continuous_fst.comp hCont

noncomputable def x_SeqPosPeak := fun (k : ℕ) => 2/((4 * k + 1) * Real.pi) -- maybe i can directly define it in [0,a] = intervalAZero
lemma h_SinPosPeak : ∀ k : ℕ, k ≥ 1 → Real.sin ((x_SeqPosPeak k)⁻¹) = 1 := by -- i don't need to show this for each x-values but only in the contraddicion
  intro k hk
  calc Real.sin ((x_SeqPosPeak k)⁻¹) = Real.sin (((4 * k + 1) * Real.pi)/2) := by
        unfold x_SeqPosPeak
        field_simp
      _ = Real.sin (Real.pi/2 + 2*k*Real.pi) := by
        field_simp
        ring_nf
      _ = Real.sin (Real.pi/2 + k*(2*Real.pi)) := by
        ring_nf
      _ = Real.sin (Real.pi/2) := by
        rw [Real.sin_add_nat_mul_two_pi]
      _ = 1 := by
        exact Real.sin_pi_div_two

lemma xSeq_tendsto_zero : Tendsto x_SeqPosPeak atTop (𝓝 0) := by
  unfold x_SeqPosPeak
  have h₁ : Tendsto (fun n : ℕ => (n) * Real.pi) atTop atTop := by
    apply Filter.Tendsto.atTop_mul_const'
    · exact Real.pi_pos
    · exact tendsto_natCast_atTop_atTop
  have h₂ : Tendsto (fun n : ℕ => n * 4 + 1) atTop atTop := by
    have h₃ : Tendsto (fun n : ℕ => n * 4 ) atTop atTop := by
      apply Filter.Tendsto.atTop_mul_const'
      · exact (by norm_num : 4 > 0)
      · exact tendsto_natCast_atTop_atTop
    sorry
  sorry

lemma TisNotPathConnSup : ¬ (IsPathConnected T)  := by
  -- Assume we hava a path from z= (0, 0) to w=(x, sin(1/x))
  -- for some x > 0
  intro hPathConn
  apply IsPathConnected.joinedIn at hPathConn
  specialize hPathConn z hz w hw
  let hPath := JoinedIn.somePath hPathConn

  -- consider the xcoordinate map wich is conituous
  -- the composition of the path with the xcoordinate map is continuous
  let xcoordPath := fun t => (hPath t).1
  have xcoordPathContinuous : Continuous (xcoordPath : unitInterval → ℝ) := by
    apply Continuous.comp
    · exact continuous_fst
    · exact hPath.continuous


  -- let t₀ the last time the path is on the y-axis
  let A : Set unitInterval := { t | (hPath t).1 = 0 }
  let t₀ : unitInterval := sSup A

  -- h_xcoordPathAtZeroEqZero = 0
    -- (3.1) let A = {t | xcoordPath t = 0}
    -- A is a closed set in unitInterval
    -- since it is the preimage of a closed set under a continuous function
    -- hence it is compact
    -- since unitInterval is compact
    -- hence it is closed
  have h_t₀_mem : t₀ ∈ A :=
    have A_nonempty : A.Nonempty := by
      use 0
      have h_xcoordPath0 : xcoordPath 0 = 0 := by
        simp only [xcoordPath]
        rw [hPath.source]
        rfl
      exact h_xcoordPath0
    have A_closed : IsClosed A := isClosed_singleton.preimage xcoordPathContinuous
    IsCompact.sSup_mem A_closed.isCompact A_nonempty
  have h_xcoordPathAtZeroEqZero : xcoordPath t₀ = 0 := h_t₀_mem

  -- the path at t₀ is (0, 0) (not so sure of this proof)
  have hPathT₀: hPath t₀ = z := by
    unfold z
    apply Prod.ext_iff.mpr

    have hPathT₀IsInT : hPath t₀ ∈ T := by
      exact hPathConn.somePath_mem t₀

    have hPathT₀_x_is_0 : (hPath t₀).1 = 0 := by
      exact h_xcoordPathAtZeroEqZero

    unfold T at hPathT₀IsInT

    constructor
    · apply h_xcoordPathAtZeroEqZero
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

  -- (3.2) let ε = 1/ 2, by continuity of the path, we can find a δ > 0 such that
  -- for all t in [t₀, t₀ + δ], ||p(t) - p(t₀)|| < 1/2
  -- hence the path is in a ball of radius 1/2 around (0, 0)

  have epsDeltaBoundAtT₀ : ∃ δ > 0, ∀ t : unitInterval, dist t t₀ < δ →
    dist (hPath t) (hPath t₀) < 1/2 := by
    have hTendstoEventually := Metric.tendsto_nhds.mp (hPath.continuousAt t₀)
    have hEventually : ∀ᶠ (t : unitInterval) in 𝓝 t₀, dist (hPath t) (hPath t₀) < 1/2 := by
      specialize hTendstoEventually (1/2)
      apply hTendstoEventually
      norm_num
    exact Metric.eventually_nhds_iff.mp hEventually

  obtain ⟨δ , hδ, ht⟩ := epsDeltaBoundAtT₀

  -- let t₁ be the a time the path is not on the y-axis
  -- t₁ is in (t₀, t₀ + δ]
  -- hence t₁ > t₀
  -- hence xcoord(p(t₁)) > 0
  -- this is terrible
  have t₀_lt_one : t₀ < 1 := by
    apply lt_of_le_of_ne
    · exact unitInterval.le_one t₀
    · intro h_eq_one
      have w_x_path : xcoordPath 1 = w_x := by
        simp only [xcoordPath, Function.comp_apply]
        rw [hPath.target]
        simp only [w, sinCurve, w_x, Prod.fst]
      have w_x_pos : w_x > 0 := by
        unfold w_x
        norm_num
      have x_eq_zero : xcoordPath 1 = 0 := by
        rw [h_eq_one] at h_t₀_mem
        exact h_t₀_mem
      rw [w_x_path] at x_eq_zero
      exact ne_of_gt w_x_pos x_eq_zero
  have Existt₁Get₀ : ∃ t₁:unitInterval, t₁ > t₀  ∧ dist t₀ t₁ < δ := by
    let s0 := (t₀ : ℝ ) -- t₀ is in unitInterval
    let s1 := min (s0 + δ/2) 1
    have s_0Delta : s0 + δ/2 > 0 := by
      apply add_pos_of_nonneg_of_pos
      · exact unitInterval.nonneg t₀
      · exact div_pos hδ (by norm_num)

    have hs1 : s1 ≥ 0 := by
      have h1 : (0 : ℝ) ≤ s0 + δ/2 := le_of_lt s_0Delta
      have h2 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
      have : (0 : ℝ) ≤ min (s0 + δ/2) 1 := le_min h1 h2
      simpa [s1] using this

    have h': s1 ≤ 1 := by
      apply min_le_right


    use ⟨s1, hs1, h'⟩
    have dist_case : dist t₀ ⟨s1, hs1, h'⟩ < δ := by
      simp_all [z, w, s1, w_x, hPath, xcoordPath, A, t₀, s0]
      refine Metric.mem_ball.mp ?_

      sorry
    constructor
    · simp only [gt_iff_lt, s1,s0, hPath, xcoordPath,← Subtype.coe_lt_coe, Subtype.coe_mk]
      apply lt_min
      · exact (lt_add_iff_pos_right _).mpr (half_pos hδ)
      · exact t₀_lt_one
    · simp only [dist_eq_norm, s1, s0, ← Subtype.coe_mk]
      exact dist_case

  obtain ⟨t₁, ht₁⟩ := Existt₁Get₀

  --- let a = xcoordPath t₁ > 0
  let a :=  xcoordPath t₁
  have ha : a > 0 := by
    unfold a xcoordPath
    have h_pathT₁ : hPath t₁ ∈ S := by

      sorry
    have h_pathT₁_x_pos : (hPath t₁).1 > 0 := by
      obtain ⟨x, hxI, hx_eq⟩ := h_pathT₁
      dsimp [PosReal] at hxI
      rw [← hx_eq]
      exact (Set.mem_Ioi.mp hxI)
    exact h_pathT₁_x_pos



  --The image x(p([t0, t1])) is connected
  let intervalT₀T₁ := Set.Icc t₀ t₁

  have xcoordPathOfT₀T₁Conn:
      IsConnected (xcoordPath '' intervalT₀T₁) := by
    have hConn : IsConnected intervalT₀T₁ := by
      unfold intervalT₀T₁
      refine isConnected_Icc ?_
      · exact le_of_lt ht₁.1
    have hCont : ContinuousOn xcoordPath intervalT₀T₁ := by
      apply xcoordPathContinuous.continuousOn

    exact hConn.image _ hCont

  -- and contains 0 = x(p(t₀)) and a = x(p(t₁))
  let zero :=  xcoordPath t₀

  have leftEnd :
      zero ∈ ( xcoordPath '' intervalT₀T₁) := by
      use t₀
      constructor
      · simp only [intervalT₀T₁, Set.mem_Icc]
        constructor
        · exact le_refl t₀
        · exact le_of_lt ht₁.1
      · rfl

  have rightEnd :
      a ∈ ( xcoordPath '' intervalT₀T₁) := by
      use t₁
      constructor
      · simp only [intervalT₀T₁, Set.mem_Icc]
        constructor
        · exact le_of_lt ht₁.1
        · exact le_refl t₁
      · rfl

  --and every connected subset of R is an interval, so
  -- (3.3) [0, a] ⊂ x(p([t0, t1])).
  let intervalAZero := Set.Icc zero a
  have intervalAZeroSubOfT₀T₁Xcoord : intervalAZero ⊆ xcoordPath '' intervalT₀T₁ := by sorry

  --let x_SeqPosPeak a sequence of x-values where sin(1/x) = 1
  -- i.e. for any k ∈ ℕ , sin(1/x_SeqPosPeak(k)) = 1
  -- x_SeqPosPeak converges to 0 as k → ∞
  -- thus there are some indicies i for wich x_SeqPosPeak i is in [0, a]

  have existsSeqInInterval : ∃ i : ℕ, x_SeqPosPeak i ∈ intervalAZero := by
    have h_conv := Metric.tendsto_nhds.mp xSeq_tendsto_zero (a/2) (by positivity)
    obtain ⟨N, hN⟩ := Filter.eventually_iff_exists_mem.mp h_conv

    -- obtain ⟨i₀, hi₀⟩ := hN.1
    sorry

  -- Now we can show that there exists s₁ in [t₀, t₁] ⊆ [t₀, t₀ + δ) such that:
  -- 1. hPath(s₁) = (*,1)
  have h_Path_s₁ :  ∃ s₁ ∈ intervalT₀T₁, (hPath s₁).2 = (1) := by

    obtain ⟨i, hi⟩ := existsSeqInInterval
    have i_ge_one : i ≥ 1 := by sorry
    obtain ⟨s₁, hs₁⟩ := intervalAZeroSubOfT₀T₁Xcoord hi
    use s₁
    constructor
    · exact hs₁.1
    · have : (hPath s₁).2 = Real.sin ((x_SeqPosPeak i)⁻¹) := by
        sorry
      rw [this]
      exact h_SinPosPeak i i_ge_one


  have h_PathContradiction : False := by

    obtain ⟨x₁, hx₁, hPathx₁⟩ := h_Path_s₁


    -- let s0 := (t₀ : ℝ ) -- t₀ is in unitInterval
    -- have h_le_one : (t₀ : ℝ) + δ ≤ 1 := by
    --   -- Proof that t₀ + δ ≤ 1 goes here
    --   -- For example, if you know δ ≤ 1 - t₀
    --   sorry

    -- let t₀Delta : unitInterval := ⟨(t₀ : ℝ) + δ, by {
    --   constructor
    --   · exact add_nonneg (unitInterval.nonneg t₀) (le_of_lt hδ)
    --   · exact h_le_one
    -- }⟩

    -- have intervalT₀T₁InDelta : intervalT₀T₁ ⊆  Set.Ico t₀ t₀Delta := by
    --   intro x hx
    --   simp only [intervalT₀T₁, Set.mem_Icc] at hx
    --   simp only [Set.mem_Ico]
    --   constructor
    --   · exact hx.1
    --   · apply lt_of_le_of_lt hx.2
    --     simp only [← Subtype.coe_lt_coe, Subtype.coe_mk]
    --     apply lt_of_lt_of_le
    --     · exact (lt_add_iff_pos_right _).mpr hδ
    --     · Existt₁Get₀.2

    have x₁_close_to_t₀ : dist x₁ t₀ < δ := by
      unfold intervalT₀T₁ at hx₁
      simp only [Set.mem_Icc] at hx₁
      have hx₁Delta: ∀ t ∈ intervalT₀T₁, dist t t₀ < δ := by
        intro t ht
        simp only [Set.mem_Icc] at ht
         --apply ht.2 --not sure
        sorry
      apply hx₁Delta
      · exact hx₁


    have path_far : dist (hPath x₁) (hPath t₀) > 1/2 := by
      rw [hPathT₀]
      unfold z
      simp only [dist_eq_norm]
      have : ‖hPath x₁ - (0, 0)‖ ≥ |(hPath x₁).2 - 0| := by
        exact norm_ge_abs_component_snd
      apply gt_of_ge_of_gt this
      simp only [hPathx₁]
      norm_num

    have path_close : dist (hPath x₁) (hPath t₀) < 1/2 := by
      apply ht
      exact x₁_close_to_t₀

    rw [hPathT₀] at path_close
    rw [hPathT₀] at path_far
    exact lt_asymm path_close path_far

  exfalso

  · exact h_PathContradiction



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
