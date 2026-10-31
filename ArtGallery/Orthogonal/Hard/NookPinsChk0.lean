module

public import ArtGallery.Orthogonal.Hard.NookPinsChk0H
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P0
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P1
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P2
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P3
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P4
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P5
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P6
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P7
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P8
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P9
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P10
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P11
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P12
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P13
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P14
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P15
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P16
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P17
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P18
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P19
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P20
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P21
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P22
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P23
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P24
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P25
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P26
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P27
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P28
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P29
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P30
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P31
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P32
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P33
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P34
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P35
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P36
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P37
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P38
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P39
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P40
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P41
public import ArtGallery.Orthogonal.Hard.NookPinsChk0P42

/-! # Copy-nook pin check: `nookPB0` (assembled from a head and 43 chunks) (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPB0_ok : nookPB0.ok 20 19 nookOr = true :=
  GCert.ok_of_parts nookPB0_head 1 43 (by decide +kernel) fun i hi =>
    match i, hi with
    | 0, _ => nookPB0_p0
    | 1, _ => nookPB0_p1
    | 2, _ => nookPB0_p2
    | 3, _ => nookPB0_p3
    | 4, _ => nookPB0_p4
    | 5, _ => nookPB0_p5
    | 6, _ => nookPB0_p6
    | 7, _ => nookPB0_p7
    | 8, _ => nookPB0_p8
    | 9, _ => nookPB0_p9
    | 10, _ => nookPB0_p10
    | 11, _ => nookPB0_p11
    | 12, _ => nookPB0_p12
    | 13, _ => nookPB0_p13
    | 14, _ => nookPB0_p14
    | 15, _ => nookPB0_p15
    | 16, _ => nookPB0_p16
    | 17, _ => nookPB0_p17
    | 18, _ => nookPB0_p18
    | 19, _ => nookPB0_p19
    | 20, _ => nookPB0_p20
    | 21, _ => nookPB0_p21
    | 22, _ => nookPB0_p22
    | 23, _ => nookPB0_p23
    | 24, _ => nookPB0_p24
    | 25, _ => nookPB0_p25
    | 26, _ => nookPB0_p26
    | 27, _ => nookPB0_p27
    | 28, _ => nookPB0_p28
    | 29, _ => nookPB0_p29
    | 30, _ => nookPB0_p30
    | 31, _ => nookPB0_p31
    | 32, _ => nookPB0_p32
    | 33, _ => nookPB0_p33
    | 34, _ => nookPB0_p34
    | 35, _ => nookPB0_p35
    | 36, _ => nookPB0_p36
    | 37, _ => nookPB0_p37
    | 38, _ => nookPB0_p38
    | 39, _ => nookPB0_p39
    | 40, _ => nookPB0_p40
    | 41, _ => nookPB0_p41
    | 42, _ => nookPB0_p42
    | _ + 43, h => absurd h (by omega)

end

end ArtGallery.Orthogonal.Hard
