import Mathlib
--Defining each set

def S : Set (ℝ × ℝ) := (fun x ↦ (x, Real.sin (x⁻¹))) '' Set.Ioi (0 : ℝ)

def Z : Set (ℝ × ℝ) := { (0, 0) }

def T : Set (ℝ × ℝ) := S ∪ Z

lemma invFunIsContinuousOnPosReal : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Ioi (0 : ℝ)) := by
  apply ContinuousOn.inv₀
  · exact continuous_id.continuousOn
  · intro x hxIsInIoi
    exact ne_of_gt hxIsInIoi

lemma sinWithinvFunIsContinuousOnPosReal : ContinuousOn (fun x : ℝ => Real.sin (x⁻¹)) (Set.Ioi (0 : ℝ)) := by
  apply Real.continuous_sin.continuousOn.comp
  · exact invFunIsContinuousOnPosReal
  · intro x hx -- getting some wierd type when checking goal
    exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a ↦ trivial) rfl -- i don't understand what's going on here (proved with exact?)

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

-- Connectedness
lemma SisConnected : IsConnected S := SIsPathConn.isConnected

lemma ZisConnected : IsConnected Z := isConnected_singleton

lemma TisNotPathConn : ¬ (IsPathConnected T)  := by
  -- unfold IsPathConnected
  by_contra h
  unfold IsPathConnected at h
  -- obtain ⟨U, h, j⟩ := h
  sorry

lemma TIsConnected : IsPreconnected T := by
    unfold IsPreconnected
    by_contra h
    push_neg at h
    obtain ⟨U, V, hU, hV, hUnion, hDisj, hSep⟩ := h

    have SisPreconnected : IsPreconnected S := SisConnected.isPreconnected
    rw[IsPreconnected] at SisPreconnected
    let U' := U ∩ S
    let V' := V ∩ S
    sorry
