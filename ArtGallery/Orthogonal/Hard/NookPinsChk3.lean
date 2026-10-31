module

public import ArtGallery.Orthogonal.Hard.NookPinsChk3H
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P0
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P1
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P2
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P3
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P4
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P5
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P6
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P7
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P8
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P9
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P10
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P11
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P12
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P13
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P14
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P15
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P16
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P17
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P18
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P19
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P20
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P21
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P22
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P23
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P24
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P25
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P26
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P27
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P28
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P29
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P30
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P31
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P32
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P33
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P34
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P35
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P36
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P37
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P38
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P39
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P40
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P41
public import ArtGallery.Orthogonal.Hard.NookPinsChk3P42

/-! # Copy-nook pin check: `nookPB1` (assembled from a head and 43 chunks) (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPB1_ok : nookPB1.ok 20 19 nookOr = true :=
  GCert.ok_of_parts nookPB1_head 1 43 (by decide +kernel) fun i hi =>
    match i, hi with
    | 0, _ => nookPB1_p0
    | 1, _ => nookPB1_p1
    | 2, _ => nookPB1_p2
    | 3, _ => nookPB1_p3
    | 4, _ => nookPB1_p4
    | 5, _ => nookPB1_p5
    | 6, _ => nookPB1_p6
    | 7, _ => nookPB1_p7
    | 8, _ => nookPB1_p8
    | 9, _ => nookPB1_p9
    | 10, _ => nookPB1_p10
    | 11, _ => nookPB1_p11
    | 12, _ => nookPB1_p12
    | 13, _ => nookPB1_p13
    | 14, _ => nookPB1_p14
    | 15, _ => nookPB1_p15
    | 16, _ => nookPB1_p16
    | 17, _ => nookPB1_p17
    | 18, _ => nookPB1_p18
    | 19, _ => nookPB1_p19
    | 20, _ => nookPB1_p20
    | 21, _ => nookPB1_p21
    | 22, _ => nookPB1_p22
    | 23, _ => nookPB1_p23
    | 24, _ => nookPB1_p24
    | 25, _ => nookPB1_p25
    | 26, _ => nookPB1_p26
    | 27, _ => nookPB1_p27
    | 28, _ => nookPB1_p28
    | 29, _ => nookPB1_p29
    | 30, _ => nookPB1_p30
    | 31, _ => nookPB1_p31
    | 32, _ => nookPB1_p32
    | 33, _ => nookPB1_p33
    | 34, _ => nookPB1_p34
    | 35, _ => nookPB1_p35
    | 36, _ => nookPB1_p36
    | 37, _ => nookPB1_p37
    | 38, _ => nookPB1_p38
    | 39, _ => nookPB1_p39
    | 40, _ => nookPB1_p40
    | 41, _ => nookPB1_p41
    | 42, _ => nookPB1_p42
    | _ + 43, h => absurd h (by omega)

end

end ArtGallery.Orthogonal.Hard
