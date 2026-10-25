-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.SubprismGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.SlopeControl
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.EndTrimming

/-! Geometry of broad subprisms inside a local packet. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set Metric
open wz_measurable_angular_selection (pd)

/-- Distance clearance implies the endpoint exclusion in the accepted prism
crossing criterion. -/
lemma not_mem_tubeEnds_of_clearance {d c : ℝ} (hc : 0 < c) (hdc : d ≤ c)
    {x v p : V} (hv : ‖v‖ = 1)
    (hleft : 4*c ≤ dist p x) (hright : 4*c ≤ dist p (x+v)) :
    p ∉ wz_coarse_tube_grains.RIS.tubeEnds d c x v := by
  intro hp
  rcases hp with hp | hp
  · obtain ⟨q, ⟨t, ht, rfl⟩, hpq⟩ := mem_thickening_iff.mp hp
    have hq : dist (x+t•v) x ≤ 2*c := by
      simpa [dist_eq_norm, norm_smul, hv, abs_of_nonneg ht.1] using ht.2
    have hh := dist_triangle p (x+t•v) x
    linarith
  · obtain ⟨q, ⟨t, ht, rfl⟩, hpq⟩ := mem_thickening_iff.mp hp
    have hq : dist (x+t•v) (x+v) ≤ 2*c := by
      rw [dist_eq_norm, show x+t•v-(x+v) = (t-1)•v by module,
        norm_smul, hv, Real.norm_eq_abs, mul_one, abs_of_nonpos (by linarith [ht.2])]
      linarith [ht.1]
    have hh := dist_triangle p (x+t•v) (x+v)
    linarith

/-- The accepted one-sixteenth crossing criterion in the local notation. -/
theorem prism_crosses_of_core_sixteen {d a b c : ℝ} (hd : 0 < d)
    (hda : 16*d ≤ a) (hdb : 16*d ≤ b) (hdc : 16*d ≤ c)
    {x v z p : V} (e : V ≃ₗᵢ[ℝ] V) (hv : ‖v‖ = 1)
    (hvlong : 1/2 ≤ |e v 2|)
    (hv0 : c*|e v 0| ≤ a/16) (hv1 : c*|e v 1| ≤ b/16)
    (hpT : p ∈ T d x v) (hp : p ∈ P (a/8) (b/8) (c/8) z e)
    (hleft : 4*c ≤ dist p x) (hright : 4*c ≤ dist p (x+v)) :
    Crosses d a b c x v z e := by
  exact wz_coarse_tube_grains.RIS.Interfaces.prism_crossing_of_core_point e hd hda hdb hdc
    hvlong hv0 hv1 ⟨⟨hpT, not_mem_tubeEnds_of_clearance (by linarith) (by linarith)
      hv hleft hright⟩, hp⟩

/-- A crossing tube in an aspect-ratio one-hundredth prism is nearly axial. -/
theorem Crosses.narrow_direction {d a b c : ℝ} (hd : 0 < d)
    (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c/100)
    {x v z : V} {e : V ≃ₗᵢ[ℝ] V} (hv : ‖v‖ = 1)
    (h : Crosses d a b c x v z e) :
    |e v 0| ≤ 6*a/c ∧ |e v 1| ≤ 6*b/c ∧ 1/2 ≤ |e v 2| := by
  have hc : 0 < c := by linarith
  obtain ⟨h0, h1⟩ := wz_coarse_tube_grains.RIS.Interfaces.crossing_prism_direction e hd
    hda hab (by linarith) hv h.2
  refine ⟨h0, h1, ?_⟩
  have h0' : |e v 0| ≤ 3/50 := h0.trans ((div_le_iff₀ hc).mpr (by linarith))
  have h1' : |e v 1| ≤ 3/50 := h1.trans ((div_le_iff₀ hc).mpr (by linarith))
  have hn := EuclideanSpace.real_norm_sq_eq (e v)
  rw [Fin.sum_univ_three, e.norm_map, hv] at hn
  have hsq0 : (e v 0)^2 ≤ (3/50 : ℝ)^2 := by
    nlinarith [sq_abs (e v 0), abs_nonneg (e v 0)]
  have hsq1 : (e v 1)^2 ≤ (3/50 : ℝ)^2 := by
    nlinarith [sq_abs (e v 1), abs_nonneg (e v 1)]
  by_contra hh
  have hh' : |e v 2| < 1/2 := lt_of_not_ge hh
  nlinarith [sq_abs (e v 2), abs_nonneg (e v 2)]

/-- Unoriented closeness to the last axis controls either transverse coordinate. -/
lemma frame_short_le_pd {u v : V} (g : V ≃ₗᵢ[ℝ] V) (hu : ‖u‖ = 1)
    (hg : ∀ p, g p 2 = inner ℝ u p) (j : Fin 3) (hj : j ≠ 2) :
    |g v j| ≤ pd v u := by
  have hgu := wz_flat_cluster_slab_filling.frame_v hu hg
  have huj : g u j = 0 := by
    fin_cases j
    · exact hgu.1
    · exact hgu.2.1
    · exact (hj rfl).elim
  apply le_min
  · have hh := wz_coarse_tube_grains.RIS.abs_rotated_coord_le g (v-u) j
    simpa only [map_sub, PiLp.sub_apply, huj, sub_zero] using hh
  · have hh := wz_coarse_tube_grains.RIS.abs_rotated_coord_le g (v+u) j
    simpa only [map_add, PiLp.add_apply, huj, add_zero] using hh

/-- A nearby tube meeting a stem has all its local shading in a narrow
transverse strip around that stem. -/
lemma local_piece_transverse_bound {d L θ : ℝ} (hL : 0 ≤ L) (hθ : 0 ≤ θ)
    {x u y v z p p₀ q : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (g : V ≃ₗᵢ[ℝ] V) (hg : ∀ p, g p 2 = inner ℝ u p)
    (hpstem : p ∈ T d x u) (hp₀stem : p₀ ∈ T d x u)
    (hpT : p ∈ T d y v) (hqT : q ∈ T d y v)
    (hpball : p ∈ ball z (L/2)) (hqball : q ∈ ball z (L/2))
    (hangle : pd v u ≤ 8*θ) : |g (q-p₀) 1| ≤ 8*d+8*θ*L := by
  have hgu := wz_flat_cluster_slab_filling.frame_v hu hg
  have hstem := tube_projected_coordinate_error hu g hp₀stem hpstem 1
  rw [hgu.2.1, mul_zero, sub_zero] at hstem
  have hnear := tube_projected_coordinate_error hv g hpT hqT 1
  have hqpd : ‖q-p‖ ≤ L := by
    have hh := dist_triangle q z p
    have hqz : dist q z < L/2 := hqball
    have hpz : dist z p < L/2 := by simpa [dist_comm] using hpball
    rw [dist_eq_norm] at hh
    linarith
  have hinner : |inner ℝ v (q-p)| ≤ L := by
    have hh := abs_real_inner_le_norm v (q-p)
    rw [hv, one_mul] at hh
    exact hh.trans hqpd
  have hshort := (frame_short_le_pd g hu hg 1 (by decide)).trans hangle
  have hprod : |inner ℝ v (q-p) * g v 1| ≤ L*(8*θ) := by
    rw [abs_mul]
    exact mul_le_mul hinner hshort (abs_nonneg _) hL
  have htri := abs_sub_abs_le_abs_sub (g (q-p) 1) (inner ℝ v (q-p)*g v 1)
  have he : g (q-p₀) 1 = g (q-p) 1 + g (p-p₀) 1 := by
    rw [show q-p₀ = (q-p)+(p-p₀) by abel, map_add]
    rfl
  rw [he]
  have hh := abs_add_le (g (q-p) 1) (g (p-p₀) 1)
  linarith


/-- A small angular packet inside a narrow prism has one longer prism containing
all pieces meeting a chosen stem. Cutting every piece by its inner core gives
exact crossings for every retained tube. -/
theorem small_packet_subprism {n : ℕ} {d a b c θ : ℝ}
    (hd : 0 < d) (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c/100)
    (hasmall : a ≤ c/1000000) (hθ : 0 < θ) (hθsmall : θ ≤ 1/1000000)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (Y : Fin n → Set V) (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hbox : ∀ i, Y i ⊆ P a b c z e) (hball : ∀ i, Y i ⊆ ball z (c/2))
    (hcross : ∀ i, (Y i).Nonempty → Crosses d a b c (x i) (v i) z e)
    (hends : ∀ i p, p ∈ Y i → 40*c ≤ dist p (x i) ∧ 40*c ≤ dist p (x i+v i))
    (i₀ : Fin n) (hi₀ : (Y i₀).Nonempty)
    (hangle : ∀ i, (Y i).Nonempty → pd (v i) (v i₀) ≤ 8*θ) :
    ∃ z' : V, ∃ g : V ≃ₗᵢ[ℝ] V,
      d ≤ 1000000*a ∧
      1000000*a ≤ 1000000*max a (θ*c) ∧
      1000000*max a (θ*c) ≤ 10*c ∧
      (∀ i, (Y i₀ ∩ Y i).Nonempty →
        Y i ⊆ P (1000000*a/8) (1000000*max a (θ*c)/8) (10*c/8) z' g) ∧
      ∀ i, (Y i ∩ P (1000000*a/8) (1000000*max a (θ*c)/8) (10*c/8) z' g).Nonempty →
        Crosses d (1000000*a) (1000000*max a (θ*c)) (10*c) (x i) (v i) z' g := by
  have ha : 0 < a := hd.trans_le hda
  have hc : 0 < c := by linarith
  obtain ⟨p₀, hp₀⟩ := hi₀
  have hstem := (hcross i₀ ⟨p₀, hp₀⟩).narrow_direction hd hda hab hbc (hv i₀)
  have hstem2 : e (v i₀) 2 ≠ 0 := by
    exact abs_pos.mp (by linarith [hstem.2.2])
  obtain ⟨g, hg2, hg0⟩ := frame_of_coordinate_slope e (hv i₀) hstem2
  let z' : V := p₀ + (g z 2-g p₀ 2) • g.symm (EuclideanSpace.single 2 1)
  have hz0 (q : V) : g (q-z') 0 = g (q-p₀) 0 := by simp [z', map_sub, map_add, map_smul]
  have hz1 (q : V) : g (q-z') 1 = g (q-p₀) 1 := by simp [z', map_sub, map_add, map_smul]
  have hz2 (q : V) : g (q-z') 2 = g (q-z) 2 := by
    simp [z', map_sub, map_add, map_smul]
  have hslope : |e (v i₀) 0 / e (v i₀) 2| ≤ 12*a/c := by
    rw [abs_div, div_le_iff₀ (abs_pos.mpr hstem2)]
    have hh := mul_le_mul_of_nonneg_left hstem.2.2 (by positivity : 0 ≤ 12*a/c)
    have he : (12*a/c)*(1/2) = 6*a/c := by ring
    rw [he] at hh
    exact hstem.1.trans hh
  have hthin (q : V) (hq : q ∈ P a b c z e) : |g (q-z') 0| ≤ 26*a := by
    have hp : p₀ ∈ P a b c z e := hbox i₀ hp₀
    have hc0 : |e (q-p₀) 0| ≤ a := by
      have he : e (q-p₀) 0 = e (q-z) 0 - e (p₀-z) 0 := by
        simp only [map_sub, PiLp.sub_apply]; ring
      rw [he]
      exact (abs_sub _ _).trans (by linarith [hq.1, hp.1])
    have hc2 : |e (q-p₀) 2| ≤ c := by
      have he : e (q-p₀) 2 = e (q-z) 2 - e (p₀-z) 2 := by
        simp only [map_sub, PiLp.sub_apply]; ring
      rw [he]
      exact (abs_sub _ _).trans (by linarith [hq.2.2, hp.2.2])
    have hprod : |(e (v i₀) 0 / e (v i₀) 2)*e (q-p₀) 2| ≤ 12*a := by
      rw [abs_mul]
      have hh := mul_le_mul hslope hc2 (abs_nonneg _) (by positivity : 0 ≤ 12*a/c)
      simpa only [div_mul_cancel₀ _ hc.ne'] using hh
    rw [hz0]
    have hh := hg0 (q-p₀)
    have ht := abs_sub (e (q-p₀) 0) ((e (v i₀) 0 / e (v i₀) 2)*e (q-p₀) 2)
    linarith
  have hdir0 (i : Fin n) (hi : (Y i).Nonempty) : |g (v i) 0| ≤ 36*a/c := by
    have hvi := (hcross i hi).narrow_direction hd hda hab hbc (hv i)
    have hv2 : |e (v i) 2| ≤ 1 := by
      simpa only [e.norm_map, hv i] using
        wz_move_two_long_grains_gain.abs_coord_le_norm (e (v i)) 2
    have hprod : |(e (v i₀) 0 / e (v i₀) 2)*e (v i) 2| ≤ 12*a/c := by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul hslope hv2 (abs_nonneg _)
        (by positivity : 0 ≤ 12*a/c)
    have hh := hg0 (v i)
    have ht := abs_sub (e (v i) 0) ((e (v i₀) 0 / e (v i₀) 2)*e (v i) 2)
    have he : 36*a/c = 2*(6*a/c+12*a/c) := by ring
    rw [he]
    linarith [hvi.1]
  have hmax : max a (θ*c) ≤ c/1000000 := by
    apply max_le hasmall
    nlinarith
  refine ⟨z', g, by linarith, by gcongr; exact le_max_left _ _, by linarith, ?_, ?_⟩
  · intro i hi q hq
    obtain ⟨p, hp, hpi⟩ := hi
    have htr := local_piece_transverse_bound hc.le hθ.le (hv i₀) (hv i) g hg2
      (hYT i₀ hp) (hYT i₀ hp₀) (hYT i hpi) (hYT i hq)
      (hball i hpi) (hball i hq) (hangle i ⟨q, hq⟩)
    have hlong : |g (q-z') 2| ≤ c/2 := by
      rw [hz2]
      exact (wz_coarse_tube_grains.RIS.abs_rotated_coord_le g (q-z) 2).trans
        (le_of_lt (by simpa only [mem_ball, dist_eq_norm] using hball i hq))
    refine ⟨?_, ?_, ?_⟩
    · have hh := hthin q (hbox i hq)
      change |g (q-z') 0| ≤ (1000000*a/8)/2
      linarith
    · change |g (q-z') 1| ≤ (1000000*max a (θ*c)/8)/2
      rw [hz1]
      linarith [le_max_left a (θ*c), le_max_right a (θ*c)]
    · change |g (q-z') 2| ≤ (10*c/8)/2
      linarith
  · intro i hi
    obtain ⟨p, hpi, hp⟩ := hi
    have hi' : (Y i).Nonempty := ⟨p, hpi⟩
    have hdir (j : Fin 3) (hj : j ≠ 2) : |g (v i) j| ≤ 8*θ :=
      (frame_short_le_pd g (hv i₀) hg2 j hj).trans (hangle i hi')
    apply prism_crosses_of_core_sixteen hd (by linarith)
      (by linarith [le_max_left a (θ*c)]) (by linarith) g (hv i)
      (abs_long_of_transverse_small g (hv i)
        (by linarith [hdir 0 (by decide)]) (by linarith [hdir 1 (by decide)]))
      _ _ (hYT i hpi) hp
      (by linarith [(hends i p hpi).1])
      (by linarith [(hends i p hpi).2])
    · have hh := (le_div_iff₀ hc).mp (hdir0 i hi')
      nlinarith
    · have hh := mul_le_mul_of_nonneg_right (hdir 1 (by decide)) hc.le
      nlinarith [le_max_right a (θ*c), le_max_left a (θ*c)]


/-- Widening the two transverse sides gives the same longer length for the
large angular scale case. -/
theorem large_packet_subprism {n : ℕ} {d a b c : ℝ}
    (hd : 0 < d) (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c/100)
    (hasmall : a ≤ c/1000000)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (Y : Fin n → Set V) (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hbox : ∀ i, Y i ⊆ P a b c z e)
    (hcross : ∀ i, (Y i).Nonempty → Crosses d a b c (x i) (v i) z e)
    (hends : ∀ i p, p ∈ Y i → 40*c ≤ dist p (x i) ∧ 40*c ≤ dist p (x i+v i)) :
    d ≤ 1000000*a ∧ 1000000*a ≤ 10*c ∧
      (∀ i, Y i ⊆ P (1000000*a/8) (10*c/8) (10*c/8) z e) ∧
      ∀ i, (Y i).Nonempty → Crosses d (1000000*a) (10*c) (10*c) (x i) (v i) z e := by
  have ha : 0 < a := hd.trans_le hda
  have hc : 0 < c := by linarith
  have hcore (i : Fin n) : Y i ⊆ P (1000000*a/8) (10*c/8) (10*c/8) z e := by
    intro p hp
    have hh := hbox i hp
    refine ⟨?_, ?_, ?_⟩
    · change |e (p-z) 0| ≤ (1000000*a/8)/2
      linarith [hh.1]
    · change |e (p-z) 1| ≤ (10*c/8)/2
      linarith [hh.2.1]
    · change |e (p-z) 2| ≤ (10*c/8)/2
      linarith [hh.2.2]
  refine ⟨by linarith, by linarith, hcore, ?_⟩
  intro i hi
  obtain ⟨p, hp⟩ := hi
  have hdir := (hcross i ⟨p, hp⟩).narrow_direction hd hda hab hbc (hv i)
  apply prism_crosses_of_core_sixteen hd (by linarith) (by linarith) (by linarith)
    e (hv i) hdir.2.2 _ _ (hYT i hp) (hcore i hp)
    (by linarith [(hends i p hp).1]) (by linarith [(hends i p hp).2])
  · have hh := (le_div_iff₀ hc).mp hdir.1
    nlinarith
  · have hh := (le_div_iff₀ hc).mp hdir.2.1
    nlinarith


/-- Common width chosen from the packet's angular scale. -/
def packetWidth (a c θ : ℝ) : ℝ :=
  if θ ≤ 1/1000000 then 1000000*max a (θ*c) else 10*c

/-- The two angular cases give one common geometric interface. -/
theorem packet_subprism {n : ℕ} {d a b c θ : ℝ}
    (hd : 0 < d) (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c/100)
    (hasmall : a ≤ c/1000000) (hθ : 0 < θ)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (Y : Fin n → Set V) (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hbox : ∀ i, Y i ⊆ P a b c z e) (hball : ∀ i, Y i ⊆ ball z (c/2))
    (hcross : ∀ i, (Y i).Nonempty → Crosses d a b c (x i) (v i) z e)
    (hends : ∀ i p, p ∈ Y i → 40*c ≤ dist p (x i) ∧ 40*c ≤ dist p (x i+v i))
    (i₀ : Fin n) (hi₀ : (Y i₀).Nonempty)
    (hangle : ∀ i, (Y i).Nonempty → pd (v i) (v i₀) ≤ 8*θ) :
    ∃ z' : V, ∃ g : V ≃ₗᵢ[ℝ] V,
      d ≤ 1000000*a ∧ 1000000*a ≤ packetWidth a c θ ∧ packetWidth a c θ ≤ 10*c ∧
      (∀ i, (Y i₀ ∩ Y i).Nonempty →
        Y i ⊆ P (1000000*a/8) (packetWidth a c θ/8) (10*c/8) z' g) ∧
      ∀ i, (Y i ∩ P (1000000*a/8) (packetWidth a c θ/8) (10*c/8) z' g).Nonempty →
        Crosses d (1000000*a) (packetWidth a c θ) (10*c) (x i) (v i) z' g := by
  by_cases hsmall : θ ≤ 1/1000000
  · simpa only [packetWidth, if_pos hsmall] using small_packet_subprism hd hda hab hbc
      hasmall hθ hsmall x v hv Y hYT z e hbox hball hcross hends i₀ hi₀ hangle
  · obtain ⟨hda', hab', hcore, hcross'⟩ :=
      large_packet_subprism hd hda hab hbc hasmall x v hv Y hYT z e hbox hcross hends
    refine ⟨z, e, ?_⟩
    simp only [packetWidth, if_neg hsmall]
    exact ⟨hda', hab', le_rfl, fun i _ => hcore i,
      fun i hi => hcross' i (hi.mono inter_subset_left)⟩

/-- Rounding the width costs at most `a/d` once `θ*c` is at least `d`. -/
theorem packetWidth_bound {d a c θ : ℝ} (hd : 0 < d) (hda : d ≤ a)
    (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hround : d ≤ θ*c) :
    θ ≤ packetWidth a c θ/(10*c) ∧
      packetWidth a c θ/(10*c) ≤ 1000000*(a/d)*θ ∧
      (1000000*a)*packetWidth a c θ*(10*c) ≤
        100000000000000*(a^2/d)*θ*c^2 := by
  have ha : 0 < a := hd.trans_le hda
  have had : 1 ≤ a/d := (one_le_div hd).mpr hda
  have hscale : θ ≤ packetWidth a c θ/(10*c) ∧
      packetWidth a c θ/(10*c) ≤ 1000000*(a/d)*θ := by
    by_cases hsmall : θ ≤ 1/1000000
    · simp only [packetWidth, if_pos hsmall]
      have hm : max a (θ*c) ≤ (a/d)*θ*c := by
        apply max_le
        · calc
            a = (a/d)*d := (div_mul_cancel₀ _ hd.ne').symm
            _ ≤ (a/d)*(θ*c) := mul_le_mul_of_nonneg_left hround (by positivity)
            _ = _ := by ring
        · have hh := mul_le_mul_of_nonneg_right had (show 0 ≤ θ*c by positivity)
          nlinarith
      constructor
      · apply (le_div_iff₀ (by positivity : 0 < 10*c)).mpr
        nlinarith [le_max_right a (θ*c)]
      · apply (div_le_iff₀ (by positivity : 0 < 10*c)).mpr
        have hh : 0 ≤ (a/d)*θ*c := by positivity
        nlinarith
    · simp only [packetWidth, if_neg hsmall, div_self (by positivity : 10*c ≠ 0)]
      refine ⟨hθ1, ?_⟩
      have hh : 1 < 1000000*θ := by linarith
      nlinarith
  refine ⟨hscale.1, hscale.2, ?_⟩
  have hw := (div_le_iff₀ (by positivity : 0 < 10*c)).mp hscale.2
  calc
    _ ≤ (1000000*a)*(1000000*(a/d)*θ*(10*c))*(10*c) := by gcongr
    _ = _ := by ring

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
