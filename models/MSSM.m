Needs["SARGES`", "~/ARGES/SARGES.m"];
Reset[];

Nf=3;
N2=2;
N3=3;
NumberOfSubgroups = 3;
Gauge[gY, U, 1, {0, 1, 1}];
Gauge[g2, SU, N2, {0, N2^2-1, 1}];
Gauge[g3, SU, N3, {0, 1, N3^2-1}];

ChiralSuperField[Q, Nf, {1/6, N2, N3}];
ChiralSuperField[L, Nf, {-1/2, N2, 1}];
ChiralSuperField[U, Nf, {-2/3, 1, N3}];
ChiralSuperField[D, Nf, {1/3, 1, N3}];
ChiralSuperField[E, Nf, {1, 1, 1}];
ChiralSuperField[Hu, 1, {1/2, N2, 1}];
ChiralSuperField[Hd, 1, {-1/2, N2, 1}];

SuperMass[\[Mu], Hu, Hd, {1&, KroneckerDelta[#1,#2]&, 1&}, 1&];
SuperYukawa[yt, Hu, Q, U, {1&, KroneckerDelta[#1,#2]&, KroneckerDelta[#2,#3]&}, KroneckerDelta[#2, 1] KroneckerDelta[#3, 1]&];
SuperYukawa[yb, Hd, Q, D, {1&, KroneckerDelta[#1,#2]&, KroneckerDelta[#2,#3]&}, KroneckerDelta[#2, 1] KroneckerDelta[#3, 1]&];
SuperYukawa[y\[Tau], Hd, L, E, {1&, KroneckerDelta[#1,#2]&, 1&}, KroneckerDelta[#2, 1] KroneckerDelta[#3, 1]&];

GauginoMass[MassB, gY];
GauginoMass[MassWB, g2];
GauginoMass[MassG, g3];

SoftBilinear[B\[Mu], Hu, Hd, {1&, KroneckerDelta[#1,#2]&, 1&}, 1&];
SoftTrilinear[Tt, Hu, Q, U, {1&, KroneckerDelta[#1,#2]&, KroneckerDelta[#2,#3]&}, KroneckerDelta[#2, 1] KroneckerDelta[#3, 1]&];
SoftTrilinear[Tb, Hd, Q, D, {1&, KroneckerDelta[#1,#2]&, KroneckerDelta[#2,#3]&}, KroneckerDelta[#2, 1] KroneckerDelta[#3, 1]&];
SoftTrilinear[T\[Tau], Hd, L, E, {1&, KroneckerDelta[#1,#2]&, 1&}, KroneckerDelta[#2, 1] KroneckerDelta[#3, 1]&];

SoftScalarMass[mHu2, Hu, Hu, {1&, KroneckerDelta[#1,#2]&, 1&}, 1&];
SoftScalarMass[mHd2, Hd, Hd, {1&, KroneckerDelta[#1,#2]&, 1&}, 1&];
SoftScalarMass[mq2, Q, Q, {1&, KroneckerDelta[#1,#2]&, KroneckerDelta[#1,#2]&}, KroneckerDelta[#1, 1] KroneckerDelta[#2, 1]&];
SoftScalarMass[ml2, L, L, {1&, KroneckerDelta[#1,#2]&, 1&}, KroneckerDelta[#1, 1] KroneckerDelta[#2, 1]&];
SoftScalarMass[mu2, U, U, {1&, 1&, KroneckerDelta[#1,#2]&}, KroneckerDelta[#1, 1] KroneckerDelta[#2, 1]&];
SoftScalarMass[md2, D, D, {1&, 1&, KroneckerDelta[#1,#2]&}, KroneckerDelta[#1, 1] KroneckerDelta[#2, 1]&];
SoftScalarMass[me2, E, E, {1&, 1&, 1&}, KroneckerDelta[#1, 1] KroneckerDelta[#2, 1]&];

VEV[vu, Hu, 1, {1, 2, 1}];
VEV[vd, Hd, 1, {1, 1, 1}];

ComputeInvariants[];

simp[a_] := Expand[a//. subInvariants //. {conj[A_] :> A}  // Simplify];

