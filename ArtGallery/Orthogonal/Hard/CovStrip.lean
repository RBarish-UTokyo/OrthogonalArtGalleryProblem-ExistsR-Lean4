module

public import ArtGallery.Orthogonal.Hard.CovInst

/-!
# The strips and the hall in the region

The floor strip `[x_L, x_R] × [−1, −1/4]` outside the open zone boxes of the floor, the ceiling
strip `[x_L, x_R] × [2H − 1/4, 2H]` outside the (mirrored) open zone boxes of the ceiling, and the
hall `[x_L, x_R] × [−1/4, 2H − 1/4]` lie in the region.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade Set

/-- A point of the strip of a half comb outside the open zone boxes lies in a gap rectangle. -/
theorem hc_gap_mem {y₀ T e : ℝ} : ∀ {zs : List FZone} {s : ℝ} {p : Point}, s ≤ p.1 → p.1 ≤ e →
    y₀ ≤ p.2 → p.2 ≤ T → (∀ Z ∈ zs, p.1 ≤ Z.L ∨ Z.R ≤ p.1) →
    ∃ r ∈ hcRects y₀ T s zs e, p ∈ r.set
  | [], s, p, h1, h2, h3, h4, _ => ⟨(s, e, y₀, T), by simp [hcRects], h1, h2, h3, h4⟩
  | Z :: zs, s, p, h1, h2, h3, h4, hZ => by
    rcases hZ Z List.mem_cons_self with h | h
    · exact ⟨(s, Z.L, y₀, T), by simp [hcRects], h1, h, h3, h4⟩
    · obtain ⟨r, hr, hp⟩ := hc_gap_mem (zs := zs) h h2 h3 h4
        (fun Z' hZ' => hZ Z' (List.mem_cons_of_mem _ hZ'))
      exact ⟨r, by simp only [hcRects, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hr), hp⟩

variable {n : ℕ} {Φ : List Constraint}

/-- The filled region of the polygon. -/
abbrev PO (n : ℕ) (Φ : List Constraint) : Set Point := (Polygon.mk ((polyO n Φ).map ratPoint)).filled

theorem hall_filled {p : Point} (h1 : (xL n Φ : ℝ) ≤ p.1) (h2 : p.1 ≤ xR n Φ) (h3 : -1 / 4 ≤ p.2)
    (h4 : p.2 ≤ 2 * Hr n Φ - 1 / 4) : p ∈ PO n Φ := by
  rw [PO, filledO]
  exact ⟨_, List.mem_cons_self, h1, h2, h3, h4⟩

theorem floor_strip_filled {p : Point} (h1 : (xL n Φ : ℝ) ≤ p.1) (h2 : p.1 ≤ xR n Φ)
    (h3 : -1 ≤ p.2) (h4 : p.2 ≤ -1 / 4) (hZ : ∀ Z ∈ zfO n Φ, p.1 ≤ Z.L ∨ Z.R ≤ p.1) :
    p ∈ PO n Φ := by
  rw [PO, filledO]
  obtain ⟨r, hr, hp⟩ := hc_gap_mem (zs := zfO n Φ) (y₀ := -1) (T := -1 / 4) h1 h2 h3 h4 hZ
  refine ⟨r, ?_, hp⟩
  simp only [regionRectsO, combRects, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl hr)

theorem ceil_strip_filled {p : Point} (h1 : (xL n Φ : ℝ) ≤ p.1) (h2 : p.1 ≤ xR n Φ)
    (h3 : 2 * Hr n Φ - 1 / 4 ≤ p.2) (h4 : p.2 ≤ 2 * Hr n Φ)
    (hZ : ∀ Z ∈ zcO n Φ, -p.1 ≤ Z.L ∨ Z.R ≤ -p.1) : p ∈ PO n Φ := by
  rw [PO, filledO]
  obtain ⟨r, hr, hp⟩ := hc_gap_mem (zs := zcO n Φ) (y₀ := -(2 * Hr n Φ))
    (T := -(2 * Hr n Φ - 1 / 4)) (s := -(xR n Φ : ℝ)) (e := -(xL n Φ : ℝ)) (p := -p)
    (by simp only [Prod.fst_neg]; linarith) (by simp only [Prod.fst_neg]; linarith)
    (by simp only [Prod.snd_neg]; linarith) (by simp only [Prod.snd_neg]; linarith)
    (by simpa only [Prod.fst_neg] using hZ)
  refine ⟨r.neg, ?_, Rect.mem_neg.2 hp⟩
  simp only [regionRectsO, combRects, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (List.mem_map.2 ⟨r, hr, rfl⟩))

end

end ArtGallery.Orthogonal.Hard
