import Mathlib

open Topology Filter

noncomputable def sinCurve := fun x ↦ (x, Real.sin (x⁻¹))
def PosReal := Set.Ioi (0 : ℝ)

def S : Set (ℝ × ℝ) := (fun x ↦ (x, Real.sin (x⁻¹))) '' Set.Ioi (0 : ℝ)

def Z : Set (ℝ × ℝ) := { (0, 0) }

def T : Set (ℝ × ℝ) := S ∪ Z

-- SineCurve is continuous and path-connected
lemma invFunIsContinuousOnPosReal : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Ioi (0 : ℝ)) := by
  apply ContinuousOn.inv₀
  · exact continuous_id.continuousOn
  · intro x hxIsInIoi
    exact ne_of_gt hxIsInIoi

lemma sinWithinvFunIsContinuousOnPosReal : ContinuousOn (fun x : ℝ => Real.sin (x⁻¹)) (Set.Ioi (0 : ℝ)) := by
  apply Real.continuous_sin.comp_continuousOn
  · exact invFunIsContinuousOnPosReal

lemma topoSinCurveIsContinuousOnPosReal : ContinuousOn (fun x ↦ (x, Real.sin (x⁻¹))) (Set.Ioi (0 : ℝ)) :=
  ContinuousOn.prod continuous_id.continuousOn sinWithinvFunIsContinuousOnPosReal

lemma posIntervalIsPathConnected : IsPathConnected (Set.Ioi (0 : ℝ)) := by
  apply Convex.isPathConnected
  · exact convex_Ioi 0
  · use 1
    simp

lemma SIsPathConn : IsPathConnected S := by
  apply IsPathConnected.image'
  · exact posIntervalIsPathConnected
  · exact topoSinCurveIsContinuousOnPosReal

-- T is connected
lemma SisConnected : IsConnected S := SIsPathConn.isConnected

lemma ZisConnected : IsConnected Z := isConnected_singleton

def Scls := closure S

local instance : Fact ((0 : ℝ) ≤ 1) := ⟨by linarith⟩
noncomputable example : CompleteLattice unitInterval := inferInstance

lemma TsubClsOfS : T ⊆ Scls := by
  intro x hx
  cases hx with
  | inl hxS => exact subset_closure hxS
  | inr hxZ =>
      rw [hxZ]
      let f :  ℕ →  ℝ × ℝ := fun n => ((n * Real.pi)⁻¹, 0)
      have hf : Tendsto f atTop (𝓝 (0, 0))  := by
        apply Filter.Tendsto.prod_mk_nhds
        · have hnMulpiAtTop : Tendsto (fun n : ℕ => n * Real.pi) atTop atTop := by
            apply Filter.Tendsto.atTop_mul_const'
            · exact Real.pi_pos
            · exact  tendsto_natCast_atTop_atTop
          exact tendsto_inv_atTop_zero.comp hnMulpiAtTop
        · exact tendsto_const_nhds
      have hf' : ∀ᶠ n in atTop, f n ∈ S := by sorry
      apply mem_closure_of_tendsto hf hf'

theorem TisConnected : IsConnected T := by
  apply IsConnected.subset_closure
  · exact SisConnected
  · tauto_set
  · exact TsubClsOfS


-- T is Path-connected
lemma TisNotPathConn : ¬ (IsPathConnected T)  := by
  unfold IsPathConnected
  by_contra h
  unfold T at h
  obtain ⟨y, hy, hx⟩ := h
  sorry


-- Define a sequence
noncomputable def mySeq (n : ℕ) : ℝ := 1 / (n + 1)

-- Show that the sequence tends to zero
example : Tendsto mySeq atTop (𝓝 0) := by
rw

sorry

