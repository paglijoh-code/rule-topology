import Cert.WA.Wall
import Cert.WA.I00
import Cert.WA.I01
import Cert.WA.I02
import Cert.WA.I03
import Cert.WA.I04
import Cert.WA.I05
import Cert.WA.I06
import Cert.WA.I07
import Cert.WA.I08
import Cert.WA.I09
import Cert.WA.I10
import Cert.WA.I11
import Cert.WA.I12
import Cert.WA.I13
import Cert.WA.I14
import Cert.WA.I15
import Cert.WA.I16
import Cert.WA.I17
import Cert.WA.I18
import Cert.WA.I19
import Cert.WA.I20
import Cert.WA.I21
import Cert.WA.I22
import Cert.WA.I23
import Cert.WA.I24
import Cert.WA.I25
import Cert.WA.I26
import Cert.WA.I27
import Cert.WA.I28
import Cert.WA.I29
import Cert.WA.I30
import Cert.WA.I31
import Cert.WA.I32
import Cert.WA.I33
import Cert.WA.I34
import Cert.WA.I35
import Cert.WA.I36
import Cert.WA.I37
import Cert.WA.I38
import Cert.WA.I39
import Cert.WA.I40
import Cert.WA.I41
import Cert.WA.I42
import Cert.WA.I43
import Cert.WA.I44
import Cert.WA.I45
import Cert.WA.I46
import Cert.WA.I47
import Cert.WA.I48
import Cert.WA.I49
import Cert.WA.I50
import Cert.WA.I51
import Cert.WA.I52
import Cert.WA.I53
import Cert.WA.I54
import Cert.WA.I55
import Cert.WA.I56
import Cert.WA.I57
import Cert.WA.I58
import Cert.WA.I59
import Cert.WA.I60
import Cert.WA.I61
import Cert.WA.I62
import Cert.WA.I63
import Cert.WA.I64
import Cert.WA.I65
import Cert.WA.I66
import Cert.WA.I67
import Cert.WA.I68
import Cert.WA.I69
import Cert.WA.I70
import Cert.WA.I71
import Cert.WA.I72
import Cert.WA.I73
import Cert.WA.I74
import Cert.WA.I75
import Cert.WA.I76
import Cert.WA.I77
import Cert.WA.I78
import Cert.WA.I79
import Cert.WA.I80
import Cert.WA.I81
import Cert.WA.I82
import Cert.WA.I83
import Cert.WA.I84
import Cert.WA.I85
import Cert.WA.I86
import Cert.WA.I87
import Cert.WA.I88
import Cert.WA.I89
import Cert.WA.I90
import Cert.WA.I91
import Cert.WA.I92
import Cert.WA.I93
import Cert.WA.I94
import Cert.WA.I95
import Cert.WA.I96
import Cert.WA.I97
import Cert.WA.I98
import Cert.WA.I99
import Cert.WA.I100
import Cert.WA.I101
import Cert.WA.I102
import Cert.WA.I103
import Cert.WA.I104
import Cert.WA.I105
import Cert.WA.I106
import Cert.WA.I107
import Cert.WA.I108
import Cert.WA.I109
import Cert.WA.I110
import Cert.WA.I111
import Cert.WA.I112
import Cert.WA.I113
import Cert.WA.I114
import Cert.WA.I115
import Cert.WA.I116
import Cert.WA.I117
import Cert.WA.I118
import Cert.WA.I119
import Cert.WA.I120
import Cert.WA.I121
import Cert.WA.I122
import Cert.WA.I123
import Cert.WA.I124
import Cert.WA.I125
import Cert.WA.I126
import Cert.WA.I127
import Cert.WA.I128
import Cert.WA.I129
import Cert.WA.I130
import Cert.WA.I131
import Cert.WA.I132
import Cert.WA.I133
import Cert.WA.I134
import Cert.WA.I135
import Cert.WA.I136
import Cert.WA.I137
import Cert.WA.I138
import Cert.WA.I139
import Cert.WA.I140
import Cert.WA.I141
import Cert.WA.I142
import Cert.WA.I143
import Cert.WA.I144
import Cert.WA.I145
import Cert.WA.I146
import Cert.WA.I147
import Cert.WA.I148
import Cert.WA.I149
import Cert.WA.I150
import Cert.WA.I151
import Cert.WA.I152
import Cert.WA.I153
import Cert.WA.I154
import Cert.WA.I155
import Cert.WA.I156
import Cert.WA.I157
import Cert.WA.I158
import Cert.WA.I159
import Cert.WA.I160
import Cert.WA.I161
import Cert.WA.I162
import Cert.WA.I163
import Cert.WA.I164
import Cert.WA.I165
import Cert.WA.I166
import Cert.WA.I167
import Cert.WA.I168
import Cert.WA.I169
import Cert.WA.I170
import Cert.WA.I171
import Cert.WA.I172
import Cert.WA.I173
import Cert.WA.I174
import Cert.WA.I175
namespace Family.Cert.WA
open Family

def endRows : Nat := 8791
def endShape : Shape := I175.s1
def endCnt : List Nat := I175.n1

theorem start_eq : applyMoves (sigma0 gper.length) [] start = some (I00.s0, I00.n0) := by
  decide +kernel

/-- The concrete initial run: the stack after `endRows` rows is `decode endShape endCnt`. -/
theorem initial_run : ∀ x, decode endShape endCnt x = St S1 gpre gper endRows x := by
  have d := start_sound S1 gpre gper start_eq
  have d0 := seg_next S1 gpre gper hS hp I00.ok I00.len
    (by decide +kernel) d
  have d1 := seg_next S1 gpre gper hS hp I01.ok I01.len
    (by decide +kernel) d0
  have d2 := seg_next S1 gpre gper hS hp I02.ok I02.len
    (by decide +kernel) d1
  have d3 := seg_next S1 gpre gper hS hp I03.ok I03.len
    (by decide +kernel) d2
  have d4 := seg_next S1 gpre gper hS hp I04.ok I04.len
    (by decide +kernel) d3
  have d5 := seg_next S1 gpre gper hS hp I05.ok I05.len
    (by decide +kernel) d4
  have d6 := seg_next S1 gpre gper hS hp I06.ok I06.len
    (by decide +kernel) d5
  have d7 := seg_next S1 gpre gper hS hp I07.ok I07.len
    (by decide +kernel) d6
  have d8 := seg_next S1 gpre gper hS hp I08.ok I08.len
    (by decide +kernel) d7
  have d9 := seg_next S1 gpre gper hS hp I09.ok I09.len
    (by decide +kernel) d8
  have d10 := seg_next S1 gpre gper hS hp I10.ok I10.len
    (by decide +kernel) d9
  have d11 := seg_next S1 gpre gper hS hp I11.ok I11.len
    (by decide +kernel) d10
  have d12 := seg_next S1 gpre gper hS hp I12.ok I12.len
    (by decide +kernel) d11
  have d13 := seg_next S1 gpre gper hS hp I13.ok I13.len
    (by decide +kernel) d12
  have d14 := seg_next S1 gpre gper hS hp I14.ok I14.len
    (by decide +kernel) d13
  have d15 := seg_next S1 gpre gper hS hp I15.ok I15.len
    (by decide +kernel) d14
  have d16 := seg_next S1 gpre gper hS hp I16.ok I16.len
    (by decide +kernel) d15
  have d17 := seg_next S1 gpre gper hS hp I17.ok I17.len
    (by decide +kernel) d16
  have d18 := seg_next S1 gpre gper hS hp I18.ok I18.len
    (by decide +kernel) d17
  have d19 := seg_next S1 gpre gper hS hp I19.ok I19.len
    (by decide +kernel) d18
  have d20 := seg_next S1 gpre gper hS hp I20.ok I20.len
    (by decide +kernel) d19
  have d21 := seg_next S1 gpre gper hS hp I21.ok I21.len
    (by decide +kernel) d20
  have d22 := seg_next S1 gpre gper hS hp I22.ok I22.len
    (by decide +kernel) d21
  have d23 := seg_next S1 gpre gper hS hp I23.ok I23.len
    (by decide +kernel) d22
  have d24 := seg_next S1 gpre gper hS hp I24.ok I24.len
    (by decide +kernel) d23
  have d25 := seg_next S1 gpre gper hS hp I25.ok I25.len
    (by decide +kernel) d24
  have d26 := seg_next S1 gpre gper hS hp I26.ok I26.len
    (by decide +kernel) d25
  have d27 := seg_next S1 gpre gper hS hp I27.ok I27.len
    (by decide +kernel) d26
  have d28 := seg_next S1 gpre gper hS hp I28.ok I28.len
    (by decide +kernel) d27
  have d29 := seg_next S1 gpre gper hS hp I29.ok I29.len
    (by decide +kernel) d28
  have d30 := seg_next S1 gpre gper hS hp I30.ok I30.len
    (by decide +kernel) d29
  have d31 := seg_next S1 gpre gper hS hp I31.ok I31.len
    (by decide +kernel) d30
  have d32 := seg_next S1 gpre gper hS hp I32.ok I32.len
    (by decide +kernel) d31
  have d33 := seg_next S1 gpre gper hS hp I33.ok I33.len
    (by decide +kernel) d32
  have d34 := seg_next S1 gpre gper hS hp I34.ok I34.len
    (by decide +kernel) d33
  have d35 := seg_next S1 gpre gper hS hp I35.ok I35.len
    (by decide +kernel) d34
  have d36 := seg_next S1 gpre gper hS hp I36.ok I36.len
    (by decide +kernel) d35
  have d37 := seg_next S1 gpre gper hS hp I37.ok I37.len
    (by decide +kernel) d36
  have d38 := seg_next S1 gpre gper hS hp I38.ok I38.len
    (by decide +kernel) d37
  have d39 := seg_next S1 gpre gper hS hp I39.ok I39.len
    (by decide +kernel) d38
  have d40 := seg_next S1 gpre gper hS hp I40.ok I40.len
    (by decide +kernel) d39
  have d41 := seg_next S1 gpre gper hS hp I41.ok I41.len
    (by decide +kernel) d40
  have d42 := seg_next S1 gpre gper hS hp I42.ok I42.len
    (by decide +kernel) d41
  have d43 := seg_next S1 gpre gper hS hp I43.ok I43.len
    (by decide +kernel) d42
  have d44 := seg_next S1 gpre gper hS hp I44.ok I44.len
    (by decide +kernel) d43
  have d45 := seg_next S1 gpre gper hS hp I45.ok I45.len
    (by decide +kernel) d44
  have d46 := seg_next S1 gpre gper hS hp I46.ok I46.len
    (by decide +kernel) d45
  have d47 := seg_next S1 gpre gper hS hp I47.ok I47.len
    (by decide +kernel) d46
  have d48 := seg_next S1 gpre gper hS hp I48.ok I48.len
    (by decide +kernel) d47
  have d49 := seg_next S1 gpre gper hS hp I49.ok I49.len
    (by decide +kernel) d48
  have d50 := seg_next S1 gpre gper hS hp I50.ok I50.len
    (by decide +kernel) d49
  have d51 := seg_next S1 gpre gper hS hp I51.ok I51.len
    (by decide +kernel) d50
  have d52 := seg_next S1 gpre gper hS hp I52.ok I52.len
    (by decide +kernel) d51
  have d53 := seg_next S1 gpre gper hS hp I53.ok I53.len
    (by decide +kernel) d52
  have d54 := seg_next S1 gpre gper hS hp I54.ok I54.len
    (by decide +kernel) d53
  have d55 := seg_next S1 gpre gper hS hp I55.ok I55.len
    (by decide +kernel) d54
  have d56 := seg_next S1 gpre gper hS hp I56.ok I56.len
    (by decide +kernel) d55
  have d57 := seg_next S1 gpre gper hS hp I57.ok I57.len
    (by decide +kernel) d56
  have d58 := seg_next S1 gpre gper hS hp I58.ok I58.len
    (by decide +kernel) d57
  have d59 := seg_next S1 gpre gper hS hp I59.ok I59.len
    (by decide +kernel) d58
  have d60 := seg_next S1 gpre gper hS hp I60.ok I60.len
    (by decide +kernel) d59
  have d61 := seg_next S1 gpre gper hS hp I61.ok I61.len
    (by decide +kernel) d60
  have d62 := seg_next S1 gpre gper hS hp I62.ok I62.len
    (by decide +kernel) d61
  have d63 := seg_next S1 gpre gper hS hp I63.ok I63.len
    (by decide +kernel) d62
  have d64 := seg_next S1 gpre gper hS hp I64.ok I64.len
    (by decide +kernel) d63
  have d65 := seg_next S1 gpre gper hS hp I65.ok I65.len
    (by decide +kernel) d64
  have d66 := seg_next S1 gpre gper hS hp I66.ok I66.len
    (by decide +kernel) d65
  have d67 := seg_next S1 gpre gper hS hp I67.ok I67.len
    (by decide +kernel) d66
  have d68 := seg_next S1 gpre gper hS hp I68.ok I68.len
    (by decide +kernel) d67
  have d69 := seg_next S1 gpre gper hS hp I69.ok I69.len
    (by decide +kernel) d68
  have d70 := seg_next S1 gpre gper hS hp I70.ok I70.len
    (by decide +kernel) d69
  have d71 := seg_next S1 gpre gper hS hp I71.ok I71.len
    (by decide +kernel) d70
  have d72 := seg_next S1 gpre gper hS hp I72.ok I72.len
    (by decide +kernel) d71
  have d73 := seg_next S1 gpre gper hS hp I73.ok I73.len
    (by decide +kernel) d72
  have d74 := seg_next S1 gpre gper hS hp I74.ok I74.len
    (by decide +kernel) d73
  have d75 := seg_next S1 gpre gper hS hp I75.ok I75.len
    (by decide +kernel) d74
  have d76 := seg_next S1 gpre gper hS hp I76.ok I76.len
    (by decide +kernel) d75
  have d77 := seg_next S1 gpre gper hS hp I77.ok I77.len
    (by decide +kernel) d76
  have d78 := seg_next S1 gpre gper hS hp I78.ok I78.len
    (by decide +kernel) d77
  have d79 := seg_next S1 gpre gper hS hp I79.ok I79.len
    (by decide +kernel) d78
  have d80 := seg_next S1 gpre gper hS hp I80.ok I80.len
    (by decide +kernel) d79
  have d81 := seg_next S1 gpre gper hS hp I81.ok I81.len
    (by decide +kernel) d80
  have d82 := seg_next S1 gpre gper hS hp I82.ok I82.len
    (by decide +kernel) d81
  have d83 := seg_next S1 gpre gper hS hp I83.ok I83.len
    (by decide +kernel) d82
  have d84 := seg_next S1 gpre gper hS hp I84.ok I84.len
    (by decide +kernel) d83
  have d85 := seg_next S1 gpre gper hS hp I85.ok I85.len
    (by decide +kernel) d84
  have d86 := seg_next S1 gpre gper hS hp I86.ok I86.len
    (by decide +kernel) d85
  have d87 := seg_next S1 gpre gper hS hp I87.ok I87.len
    (by decide +kernel) d86
  have d88 := seg_next S1 gpre gper hS hp I88.ok I88.len
    (by decide +kernel) d87
  have d89 := seg_next S1 gpre gper hS hp I89.ok I89.len
    (by decide +kernel) d88
  have d90 := seg_next S1 gpre gper hS hp I90.ok I90.len
    (by decide +kernel) d89
  have d91 := seg_next S1 gpre gper hS hp I91.ok I91.len
    (by decide +kernel) d90
  have d92 := seg_next S1 gpre gper hS hp I92.ok I92.len
    (by decide +kernel) d91
  have d93 := seg_next S1 gpre gper hS hp I93.ok I93.len
    (by decide +kernel) d92
  have d94 := seg_next S1 gpre gper hS hp I94.ok I94.len
    (by decide +kernel) d93
  have d95 := seg_next S1 gpre gper hS hp I95.ok I95.len
    (by decide +kernel) d94
  have d96 := seg_next S1 gpre gper hS hp I96.ok I96.len
    (by decide +kernel) d95
  have d97 := seg_next S1 gpre gper hS hp I97.ok I97.len
    (by decide +kernel) d96
  have d98 := seg_next S1 gpre gper hS hp I98.ok I98.len
    (by decide +kernel) d97
  have d99 := seg_next S1 gpre gper hS hp I99.ok I99.len
    (by decide +kernel) d98
  have d100 := seg_next S1 gpre gper hS hp I100.ok I100.len
    (by decide +kernel) d99
  have d101 := seg_next S1 gpre gper hS hp I101.ok I101.len
    (by decide +kernel) d100
  have d102 := seg_next S1 gpre gper hS hp I102.ok I102.len
    (by decide +kernel) d101
  have d103 := seg_next S1 gpre gper hS hp I103.ok I103.len
    (by decide +kernel) d102
  have d104 := seg_next S1 gpre gper hS hp I104.ok I104.len
    (by decide +kernel) d103
  have d105 := seg_next S1 gpre gper hS hp I105.ok I105.len
    (by decide +kernel) d104
  have d106 := seg_next S1 gpre gper hS hp I106.ok I106.len
    (by decide +kernel) d105
  have d107 := seg_next S1 gpre gper hS hp I107.ok I107.len
    (by decide +kernel) d106
  have d108 := seg_next S1 gpre gper hS hp I108.ok I108.len
    (by decide +kernel) d107
  have d109 := seg_next S1 gpre gper hS hp I109.ok I109.len
    (by decide +kernel) d108
  have d110 := seg_next S1 gpre gper hS hp I110.ok I110.len
    (by decide +kernel) d109
  have d111 := seg_next S1 gpre gper hS hp I111.ok I111.len
    (by decide +kernel) d110
  have d112 := seg_next S1 gpre gper hS hp I112.ok I112.len
    (by decide +kernel) d111
  have d113 := seg_next S1 gpre gper hS hp I113.ok I113.len
    (by decide +kernel) d112
  have d114 := seg_next S1 gpre gper hS hp I114.ok I114.len
    (by decide +kernel) d113
  have d115 := seg_next S1 gpre gper hS hp I115.ok I115.len
    (by decide +kernel) d114
  have d116 := seg_next S1 gpre gper hS hp I116.ok I116.len
    (by decide +kernel) d115
  have d117 := seg_next S1 gpre gper hS hp I117.ok I117.len
    (by decide +kernel) d116
  have d118 := seg_next S1 gpre gper hS hp I118.ok I118.len
    (by decide +kernel) d117
  have d119 := seg_next S1 gpre gper hS hp I119.ok I119.len
    (by decide +kernel) d118
  have d120 := seg_next S1 gpre gper hS hp I120.ok I120.len
    (by decide +kernel) d119
  have d121 := seg_next S1 gpre gper hS hp I121.ok I121.len
    (by decide +kernel) d120
  have d122 := seg_next S1 gpre gper hS hp I122.ok I122.len
    (by decide +kernel) d121
  have d123 := seg_next S1 gpre gper hS hp I123.ok I123.len
    (by decide +kernel) d122
  have d124 := seg_next S1 gpre gper hS hp I124.ok I124.len
    (by decide +kernel) d123
  have d125 := seg_next S1 gpre gper hS hp I125.ok I125.len
    (by decide +kernel) d124
  have d126 := seg_next S1 gpre gper hS hp I126.ok I126.len
    (by decide +kernel) d125
  have d127 := seg_next S1 gpre gper hS hp I127.ok I127.len
    (by decide +kernel) d126
  have d128 := seg_next S1 gpre gper hS hp I128.ok I128.len
    (by decide +kernel) d127
  have d129 := seg_next S1 gpre gper hS hp I129.ok I129.len
    (by decide +kernel) d128
  have d130 := seg_next S1 gpre gper hS hp I130.ok I130.len
    (by decide +kernel) d129
  have d131 := seg_next S1 gpre gper hS hp I131.ok I131.len
    (by decide +kernel) d130
  have d132 := seg_next S1 gpre gper hS hp I132.ok I132.len
    (by decide +kernel) d131
  have d133 := seg_next S1 gpre gper hS hp I133.ok I133.len
    (by decide +kernel) d132
  have d134 := seg_next S1 gpre gper hS hp I134.ok I134.len
    (by decide +kernel) d133
  have d135 := seg_next S1 gpre gper hS hp I135.ok I135.len
    (by decide +kernel) d134
  have d136 := seg_next S1 gpre gper hS hp I136.ok I136.len
    (by decide +kernel) d135
  have d137 := seg_next S1 gpre gper hS hp I137.ok I137.len
    (by decide +kernel) d136
  have d138 := seg_next S1 gpre gper hS hp I138.ok I138.len
    (by decide +kernel) d137
  have d139 := seg_next S1 gpre gper hS hp I139.ok I139.len
    (by decide +kernel) d138
  have d140 := seg_next S1 gpre gper hS hp I140.ok I140.len
    (by decide +kernel) d139
  have d141 := seg_next S1 gpre gper hS hp I141.ok I141.len
    (by decide +kernel) d140
  have d142 := seg_next S1 gpre gper hS hp I142.ok I142.len
    (by decide +kernel) d141
  have d143 := seg_next S1 gpre gper hS hp I143.ok I143.len
    (by decide +kernel) d142
  have d144 := seg_next S1 gpre gper hS hp I144.ok I144.len
    (by decide +kernel) d143
  have d145 := seg_next S1 gpre gper hS hp I145.ok I145.len
    (by decide +kernel) d144
  have d146 := seg_next S1 gpre gper hS hp I146.ok I146.len
    (by decide +kernel) d145
  have d147 := seg_next S1 gpre gper hS hp I147.ok I147.len
    (by decide +kernel) d146
  have d148 := seg_next S1 gpre gper hS hp I148.ok I148.len
    (by decide +kernel) d147
  have d149 := seg_next S1 gpre gper hS hp I149.ok I149.len
    (by decide +kernel) d148
  have d150 := seg_next S1 gpre gper hS hp I150.ok I150.len
    (by decide +kernel) d149
  have d151 := seg_next S1 gpre gper hS hp I151.ok I151.len
    (by decide +kernel) d150
  have d152 := seg_next S1 gpre gper hS hp I152.ok I152.len
    (by decide +kernel) d151
  have d153 := seg_next S1 gpre gper hS hp I153.ok I153.len
    (by decide +kernel) d152
  have d154 := seg_next S1 gpre gper hS hp I154.ok I154.len
    (by decide +kernel) d153
  have d155 := seg_next S1 gpre gper hS hp I155.ok I155.len
    (by decide +kernel) d154
  have d156 := seg_next S1 gpre gper hS hp I156.ok I156.len
    (by decide +kernel) d155
  have d157 := seg_next S1 gpre gper hS hp I157.ok I157.len
    (by decide +kernel) d156
  have d158 := seg_next S1 gpre gper hS hp I158.ok I158.len
    (by decide +kernel) d157
  have d159 := seg_next S1 gpre gper hS hp I159.ok I159.len
    (by decide +kernel) d158
  have d160 := seg_next S1 gpre gper hS hp I160.ok I160.len
    (by decide +kernel) d159
  have d161 := seg_next S1 gpre gper hS hp I161.ok I161.len
    (by decide +kernel) d160
  have d162 := seg_next S1 gpre gper hS hp I162.ok I162.len
    (by decide +kernel) d161
  have d163 := seg_next S1 gpre gper hS hp I163.ok I163.len
    (by decide +kernel) d162
  have d164 := seg_next S1 gpre gper hS hp I164.ok I164.len
    (by decide +kernel) d163
  have d165 := seg_next S1 gpre gper hS hp I165.ok I165.len
    (by decide +kernel) d164
  have d166 := seg_next S1 gpre gper hS hp I166.ok I166.len
    (by decide +kernel) d165
  have d167 := seg_next S1 gpre gper hS hp I167.ok I167.len
    (by decide +kernel) d166
  have d168 := seg_next S1 gpre gper hS hp I168.ok I168.len
    (by decide +kernel) d167
  have d169 := seg_next S1 gpre gper hS hp I169.ok I169.len
    (by decide +kernel) d168
  have d170 := seg_next S1 gpre gper hS hp I170.ok I170.len
    (by decide +kernel) d169
  have d171 := seg_next S1 gpre gper hS hp I171.ok I171.len
    (by decide +kernel) d170
  have d172 := seg_next S1 gpre gper hS hp I172.ok I172.len
    (by decide +kernel) d171
  have d173 := seg_next S1 gpre gper hS hp I173.ok I173.len
    (by decide +kernel) d172
  have d174 := seg_next S1 gpre gper hS hp I174.ok I174.len
    (by decide +kernel) d173
  have d175 := seg_next S1 gpre gper hS hp I175.ok I175.len
    (by decide +kernel) d174
  exact d175

end Family.Cert.WA
