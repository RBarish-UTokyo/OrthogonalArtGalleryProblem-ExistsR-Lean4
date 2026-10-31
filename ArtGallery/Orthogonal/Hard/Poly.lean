module

public import ArtGallery.Orthogonal.Hard.TemplatesData
public import ArtGallery.Stade.Polygon

/-!
# The orthogonal polygon of the hardness construction

The polygon `polyO n Φ`, mirroring the builder used
during development.  It is Stade's comb (rectangle
`[x_L, x_R] × [−1, 2H]` with features below the floor and above the ceiling) in which every
non-axis-parallel edge has been replaced:

* floor: the basin of the helper `H_L`, for every variable the rectangle `W2` and the floor cutter,
  for every slot the orthogonal gadget template (`oSlotFloor`);
* ceiling: for every input and every variable the rectangle `W1` and the ceiling cutter, and for
  every input the copy nook with its two helpers and the notch (`copyNookO`).

The copy nooks are not templates: their coordinates are rational functions of the instance.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain

/-! ### Inputs -/

/-- The input segments of slot `c` of the orthogonal construction, by increasing abscissa. -/
def slotInputsO (n : ℕ) (Φ : List Constraint) (c : ℕ) : List InputSeg :=
  (oTmplInputs (cKind (gadAt Φ c))).map fun i =>
    ⟨(slotG n Φ c : ℚ) + i.lx, i.pos, (cVars (gadAt Φ c)).getD i.role 0, i.ge, c, i.role⟩

/-- All input segments of the orthogonal construction. -/
def inputsO (n : ℕ) (Φ : List Constraint) : List InputSeg :=
  (List.range (paramC Φ)).flatMap (slotInputsO n Φ)

/-! ### Helper chains in canonical frames -/

/-- The chain of an AAM helper (`orthp.aam_canon`, `λ = 1`) in its canonical frame: the edge
`g = (0, 0) → f = (X, Y)` (`X, Y > 0`, interior on the left), helper point `q = (2X, 2Y)`, box
half-size `b`, arm width `w`, arm lengths `ld, lr, lu, ll` (down, right, up, left). -/
def aamCanon (X Y b w ld lr lu ll : ℚ) : List (ℚ × ℚ) :=
  [(0, 0), (2 * X - w, 0), (2 * X - w, -ld), (2 * X, -ld), (2 * X, 2 * Y - b),
    (2 * X + b, 2 * Y - b), (2 * X + b, 2 * Y - w), (2 * X + b + lr, 2 * Y - w),
    (2 * X + b + lr, 2 * Y), (2 * X + b, 2 * Y), (2 * X + b, 2 * Y + b), (2 * X + w, 2 * Y + b),
    (2 * X + w, 2 * Y + b + lu), (2 * X, 2 * Y + b + lu), (2 * X, 2 * Y + b), (2 * X - b, 2 * Y + b),
    (2 * X - b, 2 * Y + w), (2 * X - b - ll, 2 * Y + w), (2 * X - b - ll, 2 * Y), (X, 2 * Y), (X, Y)]

/-- The point `o + R(p)` for the rotation `R(u, v) = (−v, u)`. -/
def rotL (o p : ℚ × ℚ) : ℚ × ℚ := (o.1 - p.2, o.2 + p.1)

/-- The chain of the chain helper of a copy nook (`orthp.chainC_canon`) in its frame: the obtuse
end `f = (0, 0)` of the edge `f → g = (G, −h)`, the other edge at `f` going north; scale `d`
(the length of the nook segment), `x₁ = −G d/16`, box half-size `G d/16`, arm width `d/128`, arm
lengths `G d/32, d/16, d/8, 1/16` (east, up, west, down).  The helper point is
`q = (−G d/8, h d/8)` on the line of the edge. -/
def cChain (G h d : ℚ) : List (ℚ × ℚ) :=
  let x1 := -G * d / 16
  let b := G * d / 16
  let w := d / 128
  let eps := h * d / 16
  let qx := -G * d / 8
  let qy := h * d / 8
  let lu := d / 16
  let ll := d / 8
  let lr := G * d / 32
  let ld : ℚ := 1 / 16
  [(0, eps), (x1, eps), (x1, qy), (x1 + lr, qy), (x1 + lr, qy + w), (x1, qy + w), (x1, qy + b),
    (qx, qy + b), (qx, qy + b + lu), (qx - w, qy + b + lu), (qx - w, qy + b), (qx - b, qy + b),
    (qx - b, qy), (qx - b - ll, qy), (qx - b - ll, qy - w), (qx - b, qy - w), (qx - b, qy - b),
    (qx, qy - b), (qx, -h - ld), (qx + w, -h - ld), (qx + w, -h), (G, -h)]

/-- Translation by `o`. -/
def shiftQ (o p : ℚ × ℚ) : ℚ × ℚ := (o.1 + p.1, o.2 + p.2)

/-! ### Copy nooks -/

/-- The right mouth corner `R_m` of a copy nook. -/
def nookRm (a b : ℚ) (ge : Bool) (H : ℚ) : ℚ × ℚ := if ge then nookPt a b ge H else nookPs a b ge H

/-- The left mouth corner `L_m` of a copy nook. -/
def nookLm (a b : ℚ) (ge : Bool) (H : ℚ) : ℚ × ℚ := if ge then nookPs a b ge H else nookPt a b ge H

/-- The orthogonal copy nook with mouth corners `R_m, L_m` and nook segment `[N_bot, N_top]`
(ceiling order, right to left): the AAM helper of the upper wall `R_m → N_top` (beyond `N_top`),
the chain helper of the lower wall `N_bot → L_m` (beyond `N_bot`, attached along the piece of the
nook segment above `N_bot`), and the notch `[x_N − 1/2, L_m.x] × [L_m.y − 1/8, L_m.y]`. -/
def copyNookGen (Rm Lm Nt Nb : ℚ × ℚ) : List (ℚ × ℚ) :=
  let X := Nt.2 - Rm.2
  let Y := Rm.1 - Nt.1
  (aamCanon X Y (1 / 4) (1 / 32) (2 * Y + 1 / 4) (X + 1 / 4) (1 / 2) (X + 1 / 4)).map (rotL Rm) ++
  (cChain (Lm.1 - Nb.1) (Nb.2 - Lm.2) (Nt.2 - Nb.2)).map (shiftQ Nb) ++
  [(Lm.1, Lm.2 - 1 / 8), (Nb.1 - 1 / 2, Lm.2 - 1 / 8), (Nb.1 - 1 / 2, Lm.2)]

/-- The bottom end of the orthogonal nook segment: Stade's `N_bot` lowered by an eighth of the
length of Stade's nook segment, so that the piece of the segment taken by the chain helper lies
below every shadow. -/
def nookBotO (a b : ℚ) (ge : Bool) (H : ℚ) : ℚ × ℚ :=
  ((nookBot a b ge H).1, (nookBot a b ge H).2 - ((nookTop a b ge H).2 - (nookBot a b ge H).2) / 8)

/-- The orthogonal copy nook of an input at `b` copying a variable at `a`. -/
def copyNookO (a b : ℚ) (ge : Bool) (H : ℚ) : List (ℚ × ℚ) :=
  copyNookGen (nookRm a b ge H) (nookLm a b ge H) (nookTop a b ge H) (nookBotO a b ge H)

/-! ### The polygon -/

/-- The floor features, left to right: the basin of `H_L`, the variables, the slots. -/
def floorFeatsO (n : ℕ) (Φ : List Constraint) : List (List (ℚ × ℚ)) :=
  [oBasin.inst (paramH n Φ) (xL n Φ)] ++
  (List.range n).flatMap (fun k => oVarFloor.map (ITmpl.inst (paramH n Φ) (varA Φ k))) ++
  (List.range (paramC Φ)).flatMap (fun c =>
    (oSlotFloor (cKind (gadAt Φ c))).map (ITmpl.inst (paramH n Φ) (slotG n Φ c)))

/-- The ceiling features, right to left: inputs, variables, copy nooks. -/
def ceilFeatsO (n : ℕ) (Φ : List Constraint) : List (List (ℚ × ℚ)) :=
  (inputsO n Φ).reverse.flatMap (fun i => (oInputCeil i.pos).map (ITmpl.inst (paramH n Φ) i.b)) ++
  (List.range n).reverse.flatMap (fun k => oVarCeil.map (ITmpl.inst (paramH n Φ) (varA Φ k))) ++
  (List.range n).reverse.flatMap (fun k => ((inputsO n Φ).filter (fun i => i.var == k)).map
    (fun i => copyNookO (varA Φ k) i.b i.ge (paramH n Φ)))

/-- **The orthogonal polygon** (rational vertices, counterclockwise). -/
def polyO (n : ℕ) (Φ : List Constraint) : List (ℚ × ℚ) :=
  [(xL n Φ, -1)] ++ (floorFeatsO n Φ).flatten ++
    [(xR n Φ, -1), (xR n Φ, 2 * (paramH n Φ : ℚ))] ++ (ceilFeatsO n Φ).flatten ++
    [(xL n Φ, 2 * (paramH n Φ : ℚ))]

end

end ArtGallery.Orthogonal.Hard
