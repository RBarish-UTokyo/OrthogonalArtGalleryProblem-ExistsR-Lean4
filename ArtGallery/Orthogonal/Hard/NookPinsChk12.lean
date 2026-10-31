module

public import ArtGallery.Orthogonal.Hard.NookPinsChk12H
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P0
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P1
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P2
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P3
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P4
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P5
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P6
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P7
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P8
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P9
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P10
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P11
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P12
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P13
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P14
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P15
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P16
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P17
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P18
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P19
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P20
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P21
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P22
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P23
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P24
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P25
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P26
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P27
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P28
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P29
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P30
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P31
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P32
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P33
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P34
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P35
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P36
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P37
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P38
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P39
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P40
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P41
public import ArtGallery.Orthogonal.Hard.NookPinsChk12P42

/-! # Copy-nook pin check: `nookPC1` (assembled from a head and 43 chunks) (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPC1_ok : nookPC1.ok 20 19 nookOr = true :=
  GCert.ok_of_parts nookPC1_head 1 43 (by decide +kernel) fun i hi =>
    match i, hi with
    | 0, _ => nookPC1_p0
    | 1, _ => nookPC1_p1
    | 2, _ => nookPC1_p2
    | 3, _ => nookPC1_p3
    | 4, _ => nookPC1_p4
    | 5, _ => nookPC1_p5
    | 6, _ => nookPC1_p6
    | 7, _ => nookPC1_p7
    | 8, _ => nookPC1_p8
    | 9, _ => nookPC1_p9
    | 10, _ => nookPC1_p10
    | 11, _ => nookPC1_p11
    | 12, _ => nookPC1_p12
    | 13, _ => nookPC1_p13
    | 14, _ => nookPC1_p14
    | 15, _ => nookPC1_p15
    | 16, _ => nookPC1_p16
    | 17, _ => nookPC1_p17
    | 18, _ => nookPC1_p18
    | 19, _ => nookPC1_p19
    | 20, _ => nookPC1_p20
    | 21, _ => nookPC1_p21
    | 22, _ => nookPC1_p22
    | 23, _ => nookPC1_p23
    | 24, _ => nookPC1_p24
    | 25, _ => nookPC1_p25
    | 26, _ => nookPC1_p26
    | 27, _ => nookPC1_p27
    | 28, _ => nookPC1_p28
    | 29, _ => nookPC1_p29
    | 30, _ => nookPC1_p30
    | 31, _ => nookPC1_p31
    | 32, _ => nookPC1_p32
    | 33, _ => nookPC1_p33
    | 34, _ => nookPC1_p34
    | 35, _ => nookPC1_p35
    | 36, _ => nookPC1_p36
    | 37, _ => nookPC1_p37
    | 38, _ => nookPC1_p38
    | 39, _ => nookPC1_p39
    | 40, _ => nookPC1_p40
    | 41, _ => nookPC1_p41
    | 42, _ => nookPC1_p42
    | _ + 43, h => absurd h (by omega)

end

end ArtGallery.Orthogonal.Hard
