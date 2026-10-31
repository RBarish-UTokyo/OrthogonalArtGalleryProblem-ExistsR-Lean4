module

public import ArtGallery.Orthogonal.Hard.TZoneSound
public import ArtGallery.Orthogonal.Hard.CopyNookZone
public import ArtGallery.Orthogonal.Hard.ZonesCheck
public import ArtGallery.Orthogonal.Hard.Simple

/-!
# The zones of the features of the orthogonal polygon

For a floor template `t` (`fz t`) and a ceiling template (`cz t`) its checked zone, looked up in
`floorZones`, `ceilZones`; for every instantiated template and every copy nook the realised zone
(in the plane mirrored through the origin for the ceiling) is good, its feature is the instantiated
feature, and its box is known (`fzone_*`, `czone_*`, `nzone_*`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational Set

theorem ITmpl.eq_of {a b : ITmpl} (h1 : a.D = b.D) (h2 : a.pts = b.pts) : a = b := by
  cases a; cases b; simp_all

/-- Look up the zone of a template in a list of pairs. -/
def zoneLookup (l : List (ITmpl × TZone)) (t : ITmpl) : TZone :=
  (l.find? (fun p => p.1.D == t.D && p.1.pts == t.pts)).elim zone_basin Prod.snd

theorem zoneLookup_spec {l : List (ITmpl × TZone)} {t : ITmpl} (ht : ∃ z, (t, z) ∈ l) :
    (t, zoneLookup l t) ∈ l := by
  obtain ⟨z, hz⟩ := ht
  unfold zoneLookup
  cases hf : l.find? (fun p => p.1.D == t.D && p.1.pts == t.pts) with
  | none =>
    have := List.find?_eq_none.1 hf _ hz
    simp at this
  | some p =>
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have e : p.1 = t := ITmpl.eq_of hp.1 hp.2
    have hm := List.mem_of_find?_eq_some hf
    simp only [Option.elim]
    rw [← e]; exact hm

theorem mem_zip_of_mem {α β : Type*} {l : List α} {l' : List β} (hl : l'.length = l.length)
    {a : α} (ha : a ∈ l) : ∃ b, (a, b) ∈ l.zip l' := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  refine ⟨l'[k]'(by omega), ?_⟩
  have : (l.zip l')[k]'(by simp; omega) = (l[k], l'[k]'(by omega)) := List.getElem_zip
  rw [← this]; exact List.getElem_mem _

/-- The zone of a floor template. -/
def fz (t : ITmpl) : TZone := zoneLookup (allFloorTmpls.zip floorZones) t

/-- The zone of a ceiling template. -/
def cz (t : ITmpl) : TZone := zoneLookup (allCeilTmpls.zip ceilZones) t

theorem fz_facts {t : ITmpl} (ht : t ∈ allFloorTmpls) : TZoneFacts t false (fz t) := by
  have h := zoneLookup_spec (mem_zip_of_mem floorZones_len ht)
  exact tzoneFacts (List.all_eq_true.1 floorZones_ok _ h)

theorem cz_facts {t : ITmpl} (ht : t ∈ allCeilTmpls) : TZoneFacts t true (cz t) := by
  have h := zoneLookup_spec (mem_zip_of_mem ceilZones_len ht)
  exact tzoneFacts (List.all_eq_true.1 ceilZones_ok _ h)

/-! ### Floor templates -/

section Floor

variable {t : ITmpl} (ht : t ∈ allFloorTmpls) {H : ℚ} (hH : 1000 ≤ H) (ox : ℚ)
include ht

/-- The realised zone of an instantiated floor template. -/
noncomputable def fzone (t : ITmpl) (H ox : ℚ) : FZone := tzFZone t (fz t) H ox

include hH in
theorem fzone_good : (fzone t H ox).Good (-1) (-1 / 4) := by
  have h := fz_facts ht
  have hD := floorTmpl_D ht
  have := tz_good h hD (H := (H : ℝ)) (by exact_mod_cast hH) ox
  rwa [tz_F h hD, tz_T h hD] at this

theorem fzone_f : (fzone t H ox).f = (t.inst H ox).map ratPoint :=
  tz_f_floor (fz_facts ht) (floorTmpl_D ht) H ox

theorem fzone_L : (fzone t H ox).L = ((ox + t.xmin - 1 / 8 : ℚ) : ℝ) := by
  rw [fzone, tz_L (fz_facts ht) (floorTmpl_D ht)]; push_cast; simp; ring

theorem fzone_R : (fzone t H ox).R = ((ox + t.xmax + 1 / 8 : ℚ) : ℝ) := by
  rw [fzone, tz_R (fz_facts ht) (floorTmpl_D ht)]; push_cast; simp; ring

end Floor

/-! ### Ceiling templates -/

section Ceil

variable {t : ITmpl} (ht : t ∈ allCeilTmpls) {H : ℚ} (hH : 1000 ≤ H) (b : ℚ)
include ht

/-- The realised zone (mirrored through the origin) of an instantiated ceiling template. -/
noncomputable def czone (t : ITmpl) (H b : ℚ) : FZone := tzFZone t (cz t) H (-b)

include hH in
theorem czone_good : (czone t H b).Good (-(2 * (H : ℝ))) (-(2 * (H : ℝ) - 1 / 4)) := by
  have h := cz_facts ht
  have hD := ceilTmpl_D ht
  have := tz_good h hD (H := (H : ℝ)) (by exact_mod_cast hH) (-(b : ℝ))
  rw [tz_F h hD, tz_T h hD] at this
  simp only [↓reduceIte] at this
  have e1 : -(2 * (H : ℝ)) = -2 * (H : ℝ) := by ring
  have e2 : -(2 * (H : ℝ) - 1 / 4) = -2 * (H : ℝ) + 1 / 4 := by ring
  rw [e1, e2]
  unfold czone; exact this

theorem czone_f : (czone t H b).f = ((t.inst H b).map ratPoint).map (fun q => -q) :=
  tz_f_ceil (cz_facts ht) (ceilTmpl_D ht) H b

theorem czone_L : (czone t H b).L = -((b + t.xmax + 1 / 8 : ℚ) : ℝ) := by
  rw [czone, tz_L (cz_facts ht) (ceilTmpl_D ht)]; push_cast; simp; ring

theorem czone_R : (czone t H b).R = -((b + t.xmin - 1 / 8 : ℚ) : ℝ) := by
  rw [czone, tz_R (cz_facts ht) (ceilTmpl_D ht)]; push_cast; simp; ring

end Ceil

/-! ### Copy nooks -/

/-- The realised zone (mirrored through the origin) of a copy nook. -/
noncomputable def nzone (a b : ℚ) (ge : Bool) (H : ℚ) : FZone :=
  cnFZone (nookX a b ge) (nookU a b ge H) (nookG a b ge H) (3 / (2 * H - 3)) H

section Nook

variable {a b H : ℚ} (hH : 1000 ≤ H) (h1 : H + 30 ≤ b - a) (h2 : b - a ≤ 2 * H - 600) (ge : Bool)
include hH h1 h2

theorem nzone_good : (nzone a b ge H).Good (-(2 * (H : ℝ))) (-(2 * (H : ℝ) - 1 / 4)) := by
  obtain ⟨hG, hGu, hu⟩ := nook_offsets hH h1 h2 ge
  have hd3 : 0 < 2 * H - 3 := by linarith
  have he : 0 < 3 / (2 * H - 3) := by positivity
  have he' : 3 / (2 * H - 3) < 1 / 100 := by rw [div_lt_iff₀ hd3]; linarith
  have := cn_good (xN := nookX a b ge) (H := H) hG hGu hu he he'
  rw [cn_F, cn_T] at this
  have e2 : -(2 * (H : ℝ) - 1 / 4) = -(2 * (H : ℝ)) + 1 / 4 := by ring
  rw [e2]; exact this

omit hH h1 h2 in
theorem nzone_f : (nzone a b ge H).f = ((copyNookO a b ge H).map ratPoint).map (fun q => -q) := by
  rw [nzone, cn_f, copyNookO_eq]

theorem nzone_L : -((nookX a b ge + 7 : ℚ) : ℝ) ≤ (nzone a b ge H).L := by
  obtain ⟨hG, hGu, hu⟩ := nook_offsets hH h1 h2 ge
  rw [nzone, cn_L]
  have : nookX a b ge + 3 * nookU a b ge H + 3 / 8 ≤ nookX a b ge + 7 := by linarith
  have := neg_le_neg (show ((nookX a b ge + 3 * nookU a b ge H + 3 / 8 : ℚ) : ℝ) ≤
    ((nookX a b ge + 7 : ℚ) : ℝ) by exact_mod_cast this)
  exact this

theorem nzone_R : (nzone a b ge H).R ≤ -((nookX a b ge - 3 : ℚ) : ℝ) := by
  obtain ⟨hG, hGu, hu⟩ := nook_offsets hH h1 h2 ge
  rw [nzone, cn_R]
  have : nookX a b ge - 3 ≤ nookX a b ge - nookU a b ge H - 7 / 8 := by linarith
  exact neg_le_neg (by exact_mod_cast this)

end Nook

end

end ArtGallery.Orthogonal.Hard
