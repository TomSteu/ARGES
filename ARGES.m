BeginPackage["ARGES`"];
	Gauge::usage = "Specify gauge subgroup";
	WeylFermion::usage = "Add Weyl fermion";
	RealScalar::usage = "Add real scalar";
	ComplexScalar::usage = "Add complex scalar";
	YukawaMat::usage = "Add Yukawa matrix term (with h.c.) ";
	Yukawa::usage = "Add Yukawa term (with h.c.) and specify generation contraction";
	ScalarQuartic::usage = "Add scalar quartic coupling";
	VEV::usage = "Add Vacuum expectation value";
	ScalarCubic::usage = "Add scalar cubic interaction";
	ScalarLinear::usage = "Add scalar linear interaction";
	ScalarMass::usage = "Add scalar mass (bilinear term)";
	FermionMassMat::usage = "Add Fermionic mass matrix (with h.c.)";
	FermionMass::usage = "Add Fermionic mass (with h.c.) and generation contraction";
	\[Beta]::usage = "Display coupling (LoopLevel = 0) or Beta function";
	Reset::usage = "reset/initiate package";
	\[Gamma]::usage = "Anomalous dimensions for scalar or fermion fields";
	ComputeInvariants::usage = "Calculates known invariants for beta functions, saves them as rules in subInvariants";
	subInvariants::usage = "containts replacement rules for beta function invariants, use ComputeInvariants[] to calculate";
	GetGauge::usage = "Returns representation / charge for particle";
	SimplifyProduct::usage = "Simplifies tr[___] and prod[___] expressions";
	F::usage = "fermionic";
	S::usage = "scalar";
	Y::usage = "Yukawa";
	d::usage= "Dimension of Representation";
	gen::usage = "Generation Index";
	gauge::usage = "Gauge Index";
	C2::usage = "Casimir Invariant";
	S2::usage = "Dynkin Index";
	T2::usage = "Dynkin Index without Trace all particles";
	Y2::usage = "Yukawa Invariant";
	Y4::usage = "Yukawa Invariant";
	Y6::usage = "Yukawa Invariant";
	prod::usage = "product of flavour matrices";
	adj::usage = "adjoint";
	conj::usage = "complex conjugate";
	transpose::usage = "transposition";
	tr::usage = "trace of flavour matrices";
	U::usage = "Unitary Group";
	SU::usage = "Special Unitary Group";
	SO::usage = "Special Orthogonal Group";
	Sp::usage = "Special Symplectic Group";
	\[CapitalLambda]::usage = "Product of Generators";
	\[Xi]::usage = "Gauge fixing constant";
	Generator::usage = "Gauge Generator";
	subSimplifySum::usage = "Rules for advanced Simplification";
	SimplifySum::usage = "Label for advanced Simplification, to be used only within subSimplifySum";
	CheckYukawa::usage = "Checks if Yukawa interactions are generated at loop level";
	CheckFermionMass::usage = "Checks if Fermion mass term is generated at loop level";
	CheckQuartic::usage = "Checks if scalar quartic term is generated at loop level";
	CheckCubic::usage = "Checks if scalar cubic term is generated at loop level";
	CheckScalarMass::usage = "Checks if scalar mass term is generated at loop level";
	DisableNativeSums::usage = "Uses SimplifySum instead of Sum";


	Sqr[x_] := x*x;
	Eps[a_Integer, b_Integer] := (KroneckerDelta[a,1] KroneckerDelta[b,2] - KroneckerDelta[a,2] KroneckerDelta[b,1]);
	subAlpha = {\[Alpha][g_] :> Sqr[g/(4 \[Pi])]};
	NumberOfSubgroups = 1;


	Begin["ARGESp`"];
		Reset[] := Module[
			{},
			ListGauge = {};
			ListYukawa = {};
			ListQuartic = {};
			ListQuarticSym = {};
			ListVEV = {};
			WeylFermionList = {};
			AdjWeylFermionList = {};
			RealScalarList = {};
			ComplexScalarList = {};
			subInvariants = {};
			nonNumerics = {};
			YukMat = {};
			AdjYukMat = {};
			QuartMat = {{{{0}}}};
			subSimplifySum = {};
			$Assumptions = Element[KroneckerDelta[___], Reals];
			DisableNativeSums[False];
		];

		(* Interfaces to define the theory *)
		Gauge[sym_, group_, n_, reps_List] := Module[
			{},
			If[!NumberQ[NumberOfSubgroups] || !MatchQ[NumberOfSubgroups, _Integer] || NumberOfSubgroups<0,
				Message[Gauge::NAN];
				Return[];
			];
			If[Dimensions[ListGauge][[1]] >= NumberOfSubgroups,
				Message[Gauge::Full];
				Return[];
			];
			If[Dimensions[reps][[1]] != NumberOfSubgroups,
				Message[Gauge::RepMismatch];
				Return[];
			];
			AddAssumption[n];
			AddAssumptionGauge[reps];
			ListGauge = Append[ListGauge, {sym, group, n, reps}];
		];

		Gauge[sym_, group_[n_], reps_List] := Gauge[sym, group, n, reps];
		Gauge[sym_, group_, reps_List] := Gauge[sym, group, d[group], reps];

		GetGauge[part_, gauge_] := Module[
			{posP, posG},
			posG = ListPosition[ListGauge,_List?(#[[1]] == gauge &)];
			If[posG == {}, Return[0];];
			posG = posG[[1,1]];
			posP = ListPosition[ComplexScalarList, part];
			If[posP != {},
				posP = ListPosition[RealScalarList,_List?(#[[1]] == Re[part] &)];,
				posP = ListPosition[RealScalarList,_List?(#[[1]] == part &)];
			];
			If[posP != 0,
				Return[RealScalarList[[posP[[1,1]], 3, posG]]];
			];
			posP = ListPosition[AdjWeylFermionList,_List?(#[[1]] == part &)];
			If[posP != 0,
				Return[WeylFermionList[[AdjWeylFermionList[[posP[[1,1]],2]], 3, posG]]];
			];
			Return[0];
		];

		SimplifyProduct[term_] := (ContractSum2[term //. subProd //.{
			conj[conj[a_]] :> a,
			tr[adj[a_], b__] :> tr[b, adj[a]],
			(A_ tr[C___, a_, adj[b_], G___, c_, adj[d_], F___] + B_ tr[G___, c_, adj[d_], F___, C___, a_, adj[b_]]) :> (A+B)tr[C, a, adj[b], G, c, adj[d], F],
			(A_ tr[C___, a_, adj[b_], G___, c_, adj[d_], F___] + B_ tr[c_, adj[d_], F___, C___, a_, adj[b_], G___]) :> (A+B)tr[C, a, adj[b], G, c, adj[d], F],
			tr[conj[A_], adj[conj[B_]]]:>conj[tr[A,adj[B]]],
			tr[conj[A_], adj[conj[B_]], conj[C_], adj[conj[E_]]]:>conj[tr[A,adj[B],C,adj[E]]],
			tr[conj[A_], adj[conj[B_]], conj[C_], adj[conj[E_]], conj[F_], adj[conj[G_]]]:>conj[tr[A,adj[B],C,adj[E],F,adj[G]]],
			prod[conj[A_], adj[conj[B_]]][i_,j_]:>conj[prod[A,adj[B]][i,j]],
			prod[conj[A_], adj[conj[B_]], conj[C_], adj[conj[E_]]][i_,j_]:>conj[prod[A,adj[B],C,adj[E]][i,j]],
			prod[conj[A_], adj[conj[B_]], conj[C_], adj[conj[E_]], conj[F_], adj[conj[G_]]][i_,j_]:>conj[tr[A,adj[B],C,adj[E],F,adj[G]][i,j]],
			tr[A___, adj[B_], C___] :> tr[A, adj[B], C],
			prod[A___, adj[B_], C___] :> prod[A, adj[B], C],
			adj[conj[A_[i_,j_]]] :> A[j,i],
			adj[A_[i_,j_]] :> conj[A[j,i]],
			adj[conj[A_]] :> A, adj[A_]:>conj[A]
		} //. {Sum[A_, B___]:>SimplifySum[Expand[A],B]}]
		);

		WeylFermion[sym_, Nflavor_, gauge_List] := Module[
			{},
			If[Dimensions[gauge][[1]] != NumberOfSubgroups,
				Message[WeylFermion::RepMismatch];
				Return[];
			];
			If[IdxCheck[{Nflavor}],
				Message[Gen::RepInvalid];
				Return[];
			];
			If[GaugeIdxCheck[gauge],
				Message[Gauge::RepInvalid];
				Return[];
			];
			AddAssumption[Nflavor];
			AddAssumptionGauge[gauge];
			WeylFermionList = Append[WeylFermionList, {sym, Nflavor, gauge}];
			AdjWeylFermionList = Append[AdjWeylFermionList, {sym//.subProd, Length[WeylFermionList], Length[AdjWeylFermionList]+2, Length[AdjWeylFermionList]+1}];
			AdjWeylFermionList = Append[AdjWeylFermionList, {adj[sym]//.subProd, Length[WeylFermionList], Length[AdjWeylFermionList], Length[AdjWeylFermionList]}];
			YukMat = Table[If[i1 <= Length[AdjWeylFermionList] - 2 && i2 <= Length[AdjWeylFermionList] - 2, YukMat[[a, i1, i2]], 0], {a, 1, Length[RealScalarList]+1}, {i1, 1, Length[AdjWeylFermionList]}, {i2, 1, Length[AdjWeylFermionList]}];
			AdjYukMat = Table[If[i1 <= Length[AdjWeylFermionList] - 2 && i2 <= Length[AdjWeylFermionList] - 2, AdjYukMat[[a, i1, i2]], 0], {a, 1, Length[RealScalarList]+1}, {i1, 1, Length[AdjWeylFermionList]}, {i2, 1, Length[AdjWeylFermionList]}];
		];

		RealScalar[sym_, Nflavor_List, gauge_List] := Module[
			{},
			If[Dimensions[gauge][[1]] != NumberOfSubgroups || Dimensions[Nflavor][[1]] != 2,
				Message[RealScalar::RepMismatch];
				Return[];
			];
			If[IdxCheck[Nflavor],
				Message[Gen::RepInvalid];
				Return[];
			];
			If[GaugeIdxCheck[gauge],
				Message[Gauge::RepInvalid];
				Return[];
			];
			AddAssumption[Nflavor[[1]]];
			AddAssumption[Nflavor[[2]]];
			AddAssumptionGauge[gauge];
			UpdateDummy[];
			RealScalarList = Append[RealScalarList, {sym, Nflavor, gauge}];
			YukMat = Table[
				If[a <= Length[RealScalarList]-1, YukMat[[a, i1, i2]],
					If[a == Length[RealScalarList]+1, YukMat[[a-1, i1, i2]], 0]
				],
				{a, 1, Length[RealScalarList]+1},
				{i1, 1, Length[AdjWeylFermionList]},
				{i2, 1, Length[AdjWeylFermionList]}
			];
			AdjYukMat = Table[
				If[a <= Length[RealScalarList]-1, AdjYukMat[[a, i1, i2]],
					If[a == Length[RealScalarList]+1, AdjYukMat[[a-1, i1, i2]], 0]
				],
				{a, 1, Length[RealScalarList]+1},
				{i1, 1, Length[AdjWeylFermionList]},
				{i2, 1, Length[AdjWeylFermionList]}
			];
			QuartMat = Table[
				Block[
					{aa, bb, cc, dd},
					aa = If[a == Length[RealScalarList]+1, a-1,
						If[a == Length[RealScalarList], a+1, a]
					];
					bb = If[b == Length[RealScalarList]+1, b-1,
						If[b == Length[RealScalarList], b+1, b]
					];
					cc = If[c == Length[RealScalarList]+1, c-1,
						If[c == Length[RealScalarList], c+1, c]
					];
					dd = If[d == Length[RealScalarList]+1, d-1,
						If[d == Length[RealScalarList], d+1, d]
					];
					If[aa > Length[RealScalarList] || bb > Length[RealScalarList] || cc > Length[RealScalarList] || dd > Length[RealScalarList], 0, QuartMat[[aa, bb, cc, dd]]]
				],
				{a, 1, Length[RealScalarList]+1},
				{b, 1, Length[RealScalarList]+1},
				{c, 1, Length[RealScalarList]+1},
				{d, 1, Length[RealScalarList]+1}
			];
		];

		ComplexScalar[sym_, Nflavor_, Gauge_List] := Module[
			{},
			ComplexScalarList = Append[ComplexScalarList, sym];
			RealScalar[Re[sym], Nflavor, Gauge];
			RealScalar[Im[sym], Nflavor, Gauge];
		];

		VEV[sym_, Sa_, SGenIdx_List, SGaugeIdx_List, fak_:1] := Module[
			{posS},
			posS  = ListPosition[RealScalarList,_List?(#[[1]] == Sa &)];
			If[posS == {},
				Message[Scalar::UnknownParticle];
				Return[];
			];
			If[Dimensions[SGenIdx][[1]] != 2 || IdxCheck[SGenIdx],
				Message[Gen::RepMismatch];
				Return[];
			];
			If[Dimensions[SGaugeIdx][[1]] != NumberOfSubgroups || GaugeIdxCheck[SGaugeIdx],
				Message[Gauge::RepMismatch];
				Return[];
			];
			If[BosonIndexOut[posS[[1,1]], Join[SGenIdx, SGaugeIdx]],
				Message[Gen::RepMismatch];
				Message[Gauge::RepMismatch];
				Return[];
			];
			ListVEV = Append[ListVEV, {sym, fak, Join[{posS[[1,1]]}, SGenIdx, SGaugeIdx]}];
		];

		YukawaMat[sym_, Sa_, Fi_, Fj_, gauge_List, fak_:1] := Module[
			{posS, posFi, posFj},
			If[Dimensions[gauge][[1]] != NumberOfSubgroups,
				Message[Yukawa::ContractionError];
				Return[];
			];
			If[MemberQ[ComplexScalarList, Sa],
				YukawaMat[sym, Re[Sa], Fi, Fj, gauge, fak/Sqrt[2]];
				YukawaMat[sym, Im[Sa], Fi, Fj, gauge, I fak/Sqrt[2]];
				Return[];
			];
			If[MemberQ[adj/@ComplexScalarList, Sa],
				YukawaMat[sym, Re[Sa[[1]]], Fi, Fj, gauge, fak/Sqrt[2]];
				YukawaMat[sym, Im[Sa[[1]]], Fi, Fj, gauge, -I fak/Sqrt[2]];
				Return[];
			];
			posS  = ListPosition[RealScalarList,_List?(#[[1]] == Sa &)];
			posFi = ListPosition[AdjWeylFermionList,_List?(#[[1]] == Fi &)];
			posFj = ListPosition[AdjWeylFermionList,_List?(#[[1]] == Fj &)];
			If[posS == {} || posFi == {} || posFj == {},
				Message[Yukawa::UnknownParticle];,
				ListYukawa = Append[ListYukawa,{sym, posS[[1,1]], posFi[[1,1]], posFj[[1,1]], gauge, Mat[fak]&}];
				YukMat[[posS[[1,1]], posFi[[1,1]], posFj[[1,1]]]] += yuk[Length[ListYukawa]];
				YukMat[[posS[[1,1]], posFj[[1,1]], posFi[[1,1]]]] += transpose[yuk[Length[ListYukawa]]];
				AdjYukMat[[posS[[1,1]], AdjWeylFermionList[[posFj[[1,1]], 3]], AdjWeylFermionList[[posFi[[1,1]], 3]]]] += adj[yuk[Length[ListYukawa]]];
				AdjYukMat[[posS[[1,1]], AdjWeylFermionList[[posFi[[1,1]], 3]], AdjWeylFermionList[[posFj[[1,1]], 3]]]] += adj[transpose[yuk[Length[ListYukawa]]]];
			];
		];

		Yukawa[sym_, Sa_, Fi_, Fj_, gauge_List, fak_] := Module[
			{posS, posFi, posFj},
			If[Dimensions[gauge][[1]] != NumberOfSubgroups,
				Message[Yukawa::ContractionError];
				Return[];
			];
			If[MemberQ[ComplexScalarList, Sa],
				Yukawa[sym, Re[Sa], Fi, Fj, gauge, Evaluate[fak[#1,#2,#3,#4]/Sqrt[2]]&];
				Yukawa[sym, Im[Sa], Fi, Fj, gauge, Evaluate[I fak[#1,#2,#3,#4]/Sqrt[2]]&];
				Return[];
			];
			If[MemberQ[adj/@ComplexScalarList, Sa],
				Yukawa[sym, Re[Sa[[1]]], Fi, Fj, gauge, Evaluate[fak[#2,#1,#3,#4]/Sqrt[2]]&];
				Yukawa[sym, Im[Sa[[1]]], Fi, Fj, gauge, Evaluate[-I fak[#2,#1,#3,#4]/Sqrt[2]]&];
				Return[];
			];
			posS  = ListPosition[RealScalarList,_List?(#[[1]] == Sa &)];
			posFi = ListPosition[AdjWeylFermionList,_List?(#[[1]] == Fi &)];
			posFj = ListPosition[AdjWeylFermionList,_List?(#[[1]] == Fj &)];
			If[posS == {} || posFi == {} || posFj == {},
				Message[Yukawa::UnknownParticle];,
				ListYukawa = Append[ListYukawa,{sym, posS[[1,1]], posFi[[1,1]], posFj[[1,1]], gauge, fak}];
				YukMat[[posS[[1,1]], posFi[[1,1]], posFj[[1,1]]]] += yuk[Length[ListYukawa]];
				YukMat[[posS[[1,1]], posFj[[1,1]], posFi[[1,1]]]] += transpose[yuk[Length[ListYukawa]]];
				AdjYukMat[[posS[[1,1]], AdjWeylFermionList[[posFj[[1,1]], 3]], AdjWeylFermionList[[posFi[[1,1]], 3]]]] += adj[yuk[Length[ListYukawa]]];
				AdjYukMat[[posS[[1,1]], AdjWeylFermionList[[posFi[[1,1]], 3]], AdjWeylFermionList[[posFj[[1,1]], 3]]]] += adj[transpose[yuk[Length[ListYukawa]]]];
			];
		];

		ScalarQuartic[sym_, Sa_, Sb_, Sc_, Sd_, gauge_List, fak_:(1&)] := Module[
			{posA, posB, posC, posD, permList, permListPos, iter, x, x2, perm1, perm2, perm3, perm4},
			If[MemberQ[adj/@ComplexScalarList, Sa],
				ScalarQuartic[sym, Re[Sa[[1]]], Sb, Sc, Sd, gauge, (1/Sqrt[2] fak[#2,#1,#3,#4,#5,#6,#7,#8])&];
				ScalarQuartic[sym, Im[Sa[[1]]], Sb, Sc, Sd, gauge, (-I/Sqrt[2]fak[#2,#1,#3,#4,#5,#6,#7,#8])&];
				Return[];
			];
			If[MemberQ[ComplexScalarList, Sa],
				ScalarQuartic[sym, Re[Sa], Sb, Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				ScalarQuartic[sym, Im[Sa], Sb, Sc, Sd, gauge, (I/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Return[];
			];
			If[MemberQ[adj/@ComplexScalarList, Sb],
				ScalarQuartic[sym, Sa, Re[Sb[[1]]], Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#4,#3,#5,#6,#7,#8])&];
				ScalarQuartic[sym, Sa, Im[Sb[[1]]], Sc, Sd, gauge, (-I/Sqrt[2] fak[#1,#2,#4,#3,#5,#6,#7,#8])&];
				Return[];
			];
			If[MemberQ[ComplexScalarList, Sb],
				ScalarQuartic[sym, Sa, Re[Sb], Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				ScalarQuartic[sym, Sa, Im[Sb], Sc, Sd, gauge, (I/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Return[];
			];
			If[MemberQ[adj/@ComplexScalarList, Sc],
				ScalarQuartic[sym, Sa, Sb, Re[Sc[[1]]], Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#6,#5,#7,#8])&];
				ScalarQuartic[sym, Sa, Sb, Im[Sc[[1]]], Sd, gauge, (-I/Sqrt[2] fak[#1,#2,#3,#4,#6,#5,#7,#8])&];
				Return[];
			];
			If[MemberQ[ComplexScalarList, Sc],
				ScalarQuartic[sym, Sa, Sb, Re[Sc], Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				ScalarQuartic[sym, Sa, Sb, Im[Sc], Sd, gauge, (I/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Return[];
			];
			If[MemberQ[adj/@ComplexScalarList, Sd],
				ScalarQuartic[sym, Sa, Sb, Sc, Re[Sd[[1]]], gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#8,#7])&];
				ScalarQuartic[sym, Sa, Sb, Sc, Im[Sd[[1]]], gauge, (-I/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#8,#7])&];
				Return[];
			];
			If[MemberQ[ComplexScalarList, Sd],
				ScalarQuartic[sym, Sa, Sb, Sc, Re[Sd], gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				ScalarQuartic[sym, Sa, Sb, Sc, Im[Sd], gauge, (I/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Return[];
			];
			posA = ListPosition[RealScalarList,_List?(#[[1]] == Sa &)];
			posB = ListPosition[RealScalarList,_List?(#[[1]] == Sb &)];
			posC = ListPosition[RealScalarList,_List?(#[[1]] == Sc &)];
			posD = ListPosition[RealScalarList,_List?(#[[1]] == Sd &)];
			If[posA == {} || posB == {} || posC == {} || posD == {},
				Message[Scalar::UnknownParticle];,
				If[Dimensions[gauge][[1]] != NumberOfSubgroups,
					Message[Quartic::ContractionError];,
					ListQuartic = Append[ListQuartic, {sym, posA[[1,1]], posB[[1,1]], posC[[1,1]], posD[[1,1]], gauge, fak}];
					permList = PermList[List[#1,#2,#3,#4]];
					permListPos[perm_, pos_] := {posA[[1,1]], posB[[1,1]], posC[[1,1]], posD[[1,1]]}[[Position[permList[[perm]], permList[[1,pos]]][[1,1]]]];
					For[ii=1, ii<= 24, ii++,
						AppendSymQuartic[
							sym, permListPos[ii,1], permListPos[ii,2], permListPos[ii,3], permListPos[ii,4],
							Function[{x2}, x2&]/@(Function[{x}, x@@permList[[ii]]]/@gauge),
							Evaluate[1/24 fak@@Flatten[permList[[ii]] /. {#1 -> perm1, #2 -> perm2, #3 -> perm3, #4 -> perm4} //. {perm1 -> {#1, #2}, perm2 -> {#3, #4}, perm3 -> {#5, #6}, perm4 -> {#7,#8}}]]&
						];
					];
					(* remove entries with coefficient zero *)
					iter=1;
					While[True,
						If[iter > Dimensions[ListQuarticSym][[1]], Break[];];
						If[ListQuarticSym[[iter, 7]] === (0&),
							ListQuarticSym = Delete[ListQuarticSym, iter];
							QuartMat = (QuartMat /. {Quart[iter] :> 0, Quart[n_] :> Quart[n-1] /; n>iter});
							Continue[];
						];
						iter++;
					];
				];
			];
		];

		ScalarCubic[sym_, Sa_, Sb_, Sc_, gauge_List, fak_:(1&)] := Module[
			{posA, posB, posC, permList, permListPos, iter, x, x2, perm1, perm2, perm3, perm4},
			If[MemberQ[adj/@ComplexScalarList, Sa],
				ScalarCubic[sym, Re[Sa[[1]]], Sb, Sc, gauge, (1/Sqrt[2] fak[#2,#1,#3,#4,#5,#6])&];
				ScalarCubic[sym, Im[Sa[[1]]], Sb, Sc, gauge, (-I/Sqrt[2]fak[#2,#1,#3,#4,#5,#6])&];
				Return[];
			];
			If[MemberQ[ComplexScalarList, Sa],
				ScalarCubic[sym, Re[Sa], Sb, Sc, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6])&];
				ScalarCubic[sym, Im[Sa], Sb, Sc, gauge, (I/Sqrt[2] fak[#1,#2,#3,#4,#5,#6])&];
				Return[];
			];
			If[MemberQ[adj/@ComplexScalarList, Sb],
				ScalarCubic[sym, Sa, Re[Sb[[1]]], Sc, gauge, (1/Sqrt[2] fak[#1,#2,#4,#3,#5,#6])&];
				ScalarCubic[sym, Sa, Im[Sb[[1]]], Sc, gauge, (-I/Sqrt[2] fak[#1,#2,#4,#3,#5,#6])&];
				Return[];
			];
			If[MemberQ[ComplexScalarList, Sb],
				ScalarCubic[sym, Sa, Re[Sb], Sc, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6])&];
				ScalarCubic[sym, Sa, Im[Sb], Sc, gauge, (I/Sqrt[2] fak[#1,#2,#3,#4,#5,#6])&];
				Return[];
			];
			If[MemberQ[adj/@ComplexScalarList, Sc],
				ScalarCubic[sym, Sa, Sb, Re[Sc[[1]]], gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#6,#5])&];
				ScalarCubic[sym, Sa, Sb, Im[Sc[[1]]], gauge, (-I/Sqrt[2] fak[#1,#2,#3,#4,#6,#5])&];
				Return[];
			];
			If[MemberQ[ComplexScalarList, Sc],
				ScalarCubic[sym, Sa, Sb, Re[Sc], gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6])&];
				ScalarCubic[sym, Sa, Sb, Im[Sc], gauge, (I/Sqrt[2] fak[#1,#2,#3,#4,#5,#6])&];
				Return[];
			];
			posA = ListPosition[RealScalarList,_List?(#[[1]] == Sa &)];
			posB = ListPosition[RealScalarList,_List?(#[[1]] == Sb &)];
			posC = ListPosition[RealScalarList,_List?(#[[1]] == Sc &)];
			If[posA == {} || posB == {} || posC == {},
				Message[Scalar::UnknownParticle];,
				If[Dimensions[gauge][[1]] != NumberOfSubgroups,
					Message[Quartic::ContractionError];,
					ListQuartic = Append[ListQuartic, {sym, posA[[1,1]], posB[[1,1]], posC[[1,1]], Length[RealScalarList]+ 1, gauge, fak}];
					permList = PermList[List[#1,#2,#3,#4]];
					permListPos[perm_, pos_] := {posA[[1,1]], posB[[1,1]], posC[[1,1]], Length[RealScalarList]+1}[[Position[permList[[perm]], permList[[1,pos]]][[1,1]]]];
					For[ii=1, ii<= 24, ii++,
						AppendSymQuartic[
							sym, permListPos[ii,1], permListPos[ii,2], permListPos[ii,3], permListPos[ii,4],
							Function[{x2}, x2&]/@(Function[{x}, x@@permList[[ii]]]/@gauge),
							Evaluate[1/24 fak@@Flatten[permList[[ii]] /. {#1 -> perm1, #2 -> perm2, #3 -> perm3, #4 -> perm4} //. {perm1 -> {#1, #2}, perm2 -> {#3, #4}, perm3 -> {#5, #6}, perm4 -> {#7,#8}}]]&
						];
					];
					(* remove entries with coefficient zero *)
					iter=1;
					While[True,
						If[iter > Dimensions[ListQuarticSym][[1]], Break[];];
						If[ListQuarticSym[[iter, 7]] === (0&),
							ListQuarticSym = Delete[ListQuarticSym, iter];
							QuartMat = (QuartMat /. {Quart[iter] :> 0, Quart[n_] :> Quart[n-1] /; n>iter});
							Continue[];
						];
						iter++;
					];
				];
			];
		];

		ScalarMass[sym_, Sa_, Sb_, gauge_List, fak_:(1&)] := Module[
			{posA, posB, permList, permListPos, iter, x, x2, perm1, perm2, perm3, perm4},
			If[MemberQ[adj/@ComplexScalarList, Sa],
				ScalarMass[sym, Re[Sa[[1]]], Sb, gauge, (1/Sqrt[2] fak[#2,#1,#3,#4])&];
				ScalarMass[sym, Im[Sa[[1]]], Sb, gauge, (-I/Sqrt[2]fak[#2,#1,#3,#4])&];
				Return[];
			];
			If[MemberQ[ComplexScalarList, Sa],
				ScalarMass[sym, Re[Sa], Sb, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4])&];
				ScalarMass[sym, Im[Sa], Sb, gauge, (I/Sqrt[2] fak[#1,#2,#3,#4])&];
				Return[];
			];
			If[MemberQ[adj/@ComplexScalarList, Sb],
				ScalarMass[sym, Sa, Re[Sb[[1]]], gauge, (1/Sqrt[2] fak[#1,#2,#4,#3])&];
				ScalarMass[sym, Sa, Im[Sb[[1]]], gauge, (-I/Sqrt[2] fak[#1,#2,#4,#3])&];
				Return[];
			];
			If[MemberQ[ComplexScalarList, Sb],
				ScalarMass[sym, Sa, Re[Sb], gauge, (1/Sqrt[2] fak[#1,#2,#3,#4])&];
				ScalarMass[sym, Sa, Im[Sb], gauge, (I/Sqrt[2] fak[#1,#2,#3,#4])&];
				Return[];
			];
			posA = ListPosition[RealScalarList,_List?(#[[1]] == Sa &)];
			posB = ListPosition[RealScalarList,_List?(#[[1]] == Sb &)];
			If[posA == {} || posB == {},
				Message[Scalar::UnknownParticle];,
				If[Dimensions[gauge][[1]] != NumberOfSubgroups,
					Message[Quartic::ContractionError];,
					ListQuartic = Append[ListQuartic, {sym, posA[[1,1]], posB[[1,1]], Length[RealScalarList]+1, Length[RealScalarList]+1, gauge, fak}];
					permList = PermList[List[#1,#2,#3,#4]];
					permListPos[perm_, pos_] := {posA[[1,1]], posB[[1,1]], Length[RealScalarList]+1, Length[RealScalarList]+1}[[Position[permList[[perm]], permList[[1,pos]]][[1,1]]]];
					For[ii=1, ii<= 24, ii++,
						AppendSymQuartic[
							sym, permListPos[ii,1], permListPos[ii,2], permListPos[ii,3], permListPos[ii,4],
							Function[{x2}, x2&]/@(Function[{x}, x@@permList[[ii]]]/@gauge),
							Evaluate[1/24 fak@@Flatten[permList[[ii]] /. {#1 -> perm1, #2 -> perm2, #3 -> perm3, #4 -> perm4} //. {perm1 -> {#1, #2}, perm2 -> {#3, #4}, perm3 -> {#5, #6}, perm4 -> {#7,#8}}]]&
						];
					];
					(* remove entries with coefficient zero *)
					iter=1;
					While[True,
						If[iter > Dimensions[ListQuarticSym][[1]], Break[];];
						If[ListQuarticSym[[iter, 7]] === (0&),
							ListQuarticSym = Delete[ListQuarticSym, iter];
							QuartMat = (QuartMat /. {Quart[iter] :> 0, Quart[n_] :> Quart[n-1] /; n>iter});
							Continue[];
						];
						iter++;
					];
				];
			];
		];

		ScalarLinear[sym_, Sa_, gauge_List, fak_:(1&)] := Module[
			{posA, permList, permListPos, iter, x, x2, perm1, perm2, perm3, perm4},
			If[MemberQ[adj/@ComplexScalarList, Sa],
				ScalarLinear[sym, Re[Sa[[1]]], gauge, (1/Sqrt[2] fak[#2,#1])&];
				ScalarLinear[sym, Im[Sa[[1]]], gauge, (-I/Sqrt[2]fak[#2,#1])&];
				Return[];
			];
			If[MemberQ[ComplexScalarList, Sa],
				ScalarLinear[sym, Re[Sa], gauge, (1/Sqrt[2] fak[#1,#2])&];
				ScalarLinear[sym, Im[Sa], gauge, (I/Sqrt[2] fak[#1,#2])&];
				Return[];
			];
			posA = ListPosition[RealScalarList,_List?(#[[1]] == Sa &)];
			If[posA == {},
				Message[Scalar::UnknownParticle];,
				If[Dimensions[gauge][[1]] != NumberOfSubgroups,
					Message[Quartic::ContractionError];,
					ListQuartic = Append[ListQuartic, {sym, posA[[1,1]], Length[RealScalarList]+1, Length[RealScalarList]+1, Length[RealScalarList]+1, gauge, fak}];
					permList = PermList[List[#1,#2,#3,#4]];
					permListPos[perm_, pos_] := {posA[[1,1]], Length[RealScalarList]+1, Length[RealScalarList]+1, Length[RealScalarList]+1}[[Position[permList[[perm]], permList[[1,pos]]][[1,1]]]];
					For[ii=1, ii<= 24, ii++,
						AppendSymQuartic[
							sym, permListPos[ii,1], permListPos[ii,2], permListPos[ii,3], permListPos[ii,4],
							Function[{x2}, x2&]/@(Function[{x}, x@@permList[[ii]]]/@gauge),
							Evaluate[1/24 fak@@Flatten[permList[[ii]] /. {#1 -> perm1, #2 -> perm2, #3 -> perm3, #4 -> perm4} //. {perm1 -> {#1, #2}, perm2 -> {#3, #4}, perm3 -> {#5, #6}, perm4 -> {#7,#8}}]]&
						];
					];
					(* remove entries with coefficient zero *)
					iter=1;
					While[True,
						If[iter > Dimensions[ListQuarticSym][[1]], Break[];];
						If[ListQuarticSym[[iter, 7]] === (0&),
							ListQuarticSym = Delete[ListQuarticSym, iter];
							QuartMat = (QuartMat /. {Quart[iter] :> 0, Quart[n_] :> Quart[n-1] /; n>iter});
							Continue[];
						];
						iter++;
					];
				];
			];
		];

		FermionMassMat[sym_, Fi_, Fj_, gauge_List, fak_:1] := Module[
			{posFi, posFj, x},
			If[Dimensions[gauge][[1]] != NumberOfSubgroups,
				Message[Yukawa::ContractionError];
				Return[];
			];
			posFi = ListPosition[AdjWeylFermionList,_List?(#[[1]] == Fi &)];
			posFj = ListPosition[AdjWeylFermionList,_List?(#[[1]] == Fj &)];
			If[posFi == {} || posFj == {},
				Message[Fermion::UnknownParticle];,
				ListYukawa = Append[ListYukawa, {sym, Length[RealScalarList]+1, posFi[[1,1]], posFj[[1,1]], Function[{x}, Evaluate[x[#2,#3]]&]/@gauge, Mat[fak]&}];
				YukMat[[Length[RealScalarList]+1, posFi[[1,1]], posFj[[1,1]]]] += yuk[Length[ListYukawa]];
				YukMat[[Length[RealScalarList]+1, posFj[[1,1]], posFi[[1,1]]]] += transpose[yuk[Length[ListYukawa]]];
				AdjYukMat[[Length[RealScalarList]+1, AdjWeylFermionList[[posFj[[1,1]], 3]], AdjWeylFermionList[[posFi[[1,1]], 3]]]] += adj[yuk[Length[ListYukawa]]];
				AdjYukMat[[Length[RealScalarList]+1, AdjWeylFermionList[[posFi[[1,1]], 3]], AdjWeylFermionList[[posFj[[1,1]], 3]]]] += adj[transpose[yuk[Length[ListYukawa]]]];
			];
		];

		FermionMass[sym_, Fi_, Fj_, gauge_List, fak_] := Module[
			{posS, posFi, posFj},
			If[Dimensions[gauge][[1]] != NumberOfSubgroups,
				Message[Yukawa::ContractionError];
				Return[];
			];
			posFi = ListPosition[AdjWeylFermionList,_List?(#[[1]] == Fi &)];
			posFj = ListPosition[AdjWeylFermionList,_List?(#[[1]] == Fj &)];
			If[posFi == {} || posFj == {},
				Message[Fermion::UnknownParticle];,
				ListYukawa = Append[ListYukawa, {sym, Length[RealScalarList]+1, posFi[[1,1]], posFj[[1,1]], Function[{x}, Evaluate[x[#2,#3]]&]/@gauge, Evaluate[fak[#3,#4]]&}];
				YukMat[[Length[RealScalarList]+1, posFi[[1,1]], posFj[[1,1]]]] += yuk[Length[ListYukawa]];
				YukMat[[Length[RealScalarList]+1, posFj[[1,1]], posFi[[1,1]]]] += transpose[yuk[Length[ListYukawa]]];
				AdjYukMat[[Length[RealScalarList]+1, AdjWeylFermionList[[posFj[[1,1]], 3]], AdjWeylFermionList[[posFi[[1,1]], 3]]]] += adj[yuk[Length[ListYukawa]]];
				AdjYukMat[[Length[RealScalarList]+1, AdjWeylFermionList[[posFi[[1,1]], 3]], AdjWeylFermionList[[posFj[[1,1]], 3]]]] += adj[transpose[yuk[Length[ListYukawa]]]];
			];
		];

		(* Increment dummy field number before adding new scalar *)
		UpdateDummy[] := Module[
			{},
			If[ListYukawa != {},
				Function[{x}, If[ListYukawa[[x,2]] >= Length[RealScalarList] + 1, ListYukawa[[x,2]] += 1;];]/@Range[Dimensions[ListYukawa][[1]]];
			];
			If[ListQuartic != {},
				Function[{x},
					If[ListQuartic[[x,2]] >= Length[RealScalarList] + 1, ListQuartic[[x,2]] += 1;];
					If[ListQuartic[[x,3]] >= Length[RealScalarList] + 1, ListQuartic[[x,3]] += 1;];
					If[ListQuartic[[x,4]] >= Length[RealScalarList] + 1, ListQuartic[[x,4]] += 1;];
					If[ListQuartic[[x,5]] >= Length[RealScalarList] + 1, ListQuartic[[x,5]] += 1;];
				]/@Range[Dimensions[ListQuartic][[1]]];
			];
			If[ListQuarticSym != {},
				Function[{x},
					If[ListQuarticSym[[x,2]] >= Length[RealScalarList] + 1, ListQuarticSym[[x,2]] += 1;];
					If[ListQuarticSym[[x,3]] >= Length[RealScalarList] + 1, ListQuarticSym[[x,3]] += 1;];
					If[ListQuarticSym[[x,4]] >= Length[RealScalarList] + 1, ListQuarticSym[[x,4]] += 1;];
					If[ListQuarticSym[[x,5]] >= Length[RealScalarList] + 1, ListQuarticSym[[x,5]] += 1;];
				]/@Range[Dimensions[ListQuartic][[1]]];
			];
		];

		(* Symmetrize and resum Quartic into seperate list *)
		AppendSymQuartic[sym_, pa_, pb_, pc_, pd_, gauge_, fak_] := Module[
			{pos, ii, dum1, dum2, dum3, dum4},
			pos = 0;
			For[ii = 1, ii <= Dimensions[ListQuarticSym][[1]], ii++,
				If[
					ListQuarticSym[[ii,1]] == sym && ListQuarticSym[[ii,2]] == pa && ListQuarticSym[[ii,3]] == pb && ListQuarticSym[[ii,4]] == pc && ListQuarticSym[[ii,5]] == pd && And@@(Function[{x}, ListQuarticSym[[ii,6,x]][dum1, dum2, dum3, dum4] === gauge[[x]][dum1, dum2, dum3, dum4]]/@Range[NumberOfSubgroups]),
					pos = ii;
				];
			];
			If[pos == 0,
				ListQuarticSym = Append[ListQuarticSym, {sym, pa, pb, pc, pd, gauge, fak}];
				QuartMat[[pa,pb,pc,pd]] += Quart[Length[ListQuarticSym]];,
				ListQuarticSym[[pos, 7]] = Evaluate[ListQuarticSym[[pos, 7]][#1,#2,#3,#4,#5,#6,#7,#8] + fak[#1,#2,#3,#4,#5,#6,#7,#8]]&;
			];
		];

		(* add assumptions for non-numeric input *)
		AddAssumption[sym_] := Module[
			{},
			If[NumberQ[sym], Return[];];
			If[MemberQ[nonNumerics,sym], Return[];];
			$Assumptions=$Assumptions&&Element[sym, Integers]&&(sym>1);
			nonNumerics = Append[nonNumerics,sym];
		];

		(* add assumptions for gauge list - fish out U(1) cases *)
		AddAssumptionGauge[symList] := Module[
			{i},
			If[Length[symList] > NumberOfSubgroups, Return[];];
			For[i=1, i <= Length[symList], i++,
				If[ListGauge[[i,3]] === 1, Coninue[];];
				AddAssumption[symList[[i]]];
			];
		];

		(* Check that indices are Integers *)

		IdxCheck[IdxList_] := Or@@((Function[{x}, (NumberQ[x] && !(IntegerQ[x] && (x>0)))])/@Flatten[IdxList]);

		GaugeIdxCheck[GaugeList_] := Module[
			{glist},
			If[ListGauge == {}, Return[False];];
			glist = GaugeList;
			For[ii = Dimensions[ListGauge][[1]], ii>=1, ii--,
				If[ListGauge[[ii,3]] === 1,
					glist=Delete[glist,ii];
				];
			];
			Return[Or@@((Function[{x}, (NumberQ[x] && !(IntegerQ[x] && (x>0)))])/@glist)];
		];


		(* Interfaces for Beta functions *)

		(* gauge coupling *)
		\[Beta][\[Alpha][sym_], loop_] := Module[
			{pos},
			pos = ListPosition[ListGauge,_List?(#[[1]] == sym &)];
			If[pos != {},
				Return[BetaGauge[pos[[1,1]], loop]//SimplifyProduct];
			];
			Return[0];
		];

		\[Beta][sym_, loop_] := Module[
			{pos},
			(* gauge coupling *)
			pos = ListPosition[ListGauge,_List?(#[[1]] == sym &)];
			If[pos != {},
				If[loop =!= 0,
					Return[Expand[(\[Beta][\[Alpha][sym], loop] Sqr[4 Pi]/(2 sym))//.subAlpha]//SimplifyProduct];,
					Return[sym//SimplifyProduct];
				];
			];
			(* VEV *)
			pos = ListPosition[ListVEV,_List?(#[[1]] == sym &)];
			If[pos != {},
				Return[BetaVEV[pos[[1,1]], loop]//SimplifyProduct];
			];
		];

		(* Yukawa coupling *)
		\[Beta][SType_, FType1_, FType2_, SList_List, FList1_List, FList2_List, loop_ ] := Module[
			{posS, posF1, posF2},
			If[MemberQ[ComplexScalarList, _?((# === SType)&)],
				Return[Sqrt[2]\[Beta][Re[SType], FType1, FType2, SList, FList1, FList2, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType)&)],
				Return[Sqrt[2]\[Beta][Re[SType[[1]]], FType1, FType2, Join[{SList[[2]], SList[[1]]}, SList[[3;;]]], FList1, FList2, loop]];
			];
			posS  = ListPosition[RealScalarList,_List?(#[[1]] == SType &)];
			posF1 = ListPosition[AdjWeylFermionList,_List?(#[[1]] == FType1 &)];
			posF2 = ListPosition[AdjWeylFermionList,_List?(#[[1]] == FType2 &)];
			If[posS == {} || posF1 == {} || posF2 == {},
				Message[Yukawa::UnknownParticle];
				Return[];
			];
			If[BosonIndexOut[posS[[1,1]], SList] || FermionIndexOut[AdjWeylFermionList[[posF1[[1,1]], 2]], FList1] || FermionIndexOut[AdjWeylFermionList[[posF2[[1,1]], 2]], FList2],
				Return[0];
			];
			Return[BetaYukawa[posS[[1,1]], posF1[[1,1]], posF2[[1,1]], SList, FList1, FList2, loop]//SimplifyProduct];
		]/;(Dimensions[FList1][[1]] == NumberOfSubgroups+1 && Dimensions[FList2][[1]] == NumberOfSubgroups+1);

		(* Scalar Quartic *)
		\[Beta][SType1_, SType2_, SType3_, SType4_, SList1_, SList2_, SList3_, SList4_, loop_] := Module[
			{pos1, pos2, pos3, pos4},
			If[MemberQ[ComplexScalarList, _?((# === SType1)&)],
				Return[Sqrt[2] \[Beta][Re[SType1], SType2, SType3, SType4, SList1, SList2, SList3, SList4, loop]];
			];
			If[MemberQ[ComplexScalarList, _?((# === SType2)&)],
				Return[Sqrt[2] \[Beta][SType1, Re[SType2], SType3, SType4, SList1, SList2, SList3, SList4, loop]];
			];
			If[MemberQ[ComplexScalarList, _?((# === SType3)&)] ,
				Return[Sqrt[2] \[Beta][SType1, SType2, Re[SType3], SType4, SList1, SList2, SList3, SList4, loop]];
			];
			If[MemberQ[ComplexScalarList, _?((# === SType4)&)],
				Return[Sqrt[2] \[Beta][SType1, SType2, SType3, Re[SType4], SList1, SList2, SList3, SList4, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType1)&)],
				Return[Sqrt[2] \[Beta][Re[SType1[[1]]], SType2, SType3, SType4, Join[{SList1[[2]], SList1[[1]]},SList1[[3;;]]], SList2, SList3, SList4, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType2)&)],
				Return[Sqrt[2] \[Beta][SType1, Re[SType2[[1]]], SType3, SType4, SList1, Join[{SList2[[2]], SList2[[1]]},SList2[[3;;]]], SList3, SList4, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType3)&)],
				Return[Sqrt[2] \[Beta][SType1, SType2, Re[SType3[[1]]], SType4, SList1, SList2, Join[{SList3[[2]], SList3[[1]]},SList3[[3;;]]], SList4, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType4)&)],
				Return[Sqrt[2] \[Beta][SType1, SType2, SType3, Re[SType4[[1]]], SList1, SList2, SList3, Join[{SList4[[2]], SList4[[1]]},SList4[[3;;]]], loop]];
			];
			pos1  = ListPosition[RealScalarList,_List?(#[[1]] == SType1 &)];
			pos2  = ListPosition[RealScalarList,_List?(#[[1]] == SType2 &)];
			pos3  = ListPosition[RealScalarList,_List?(#[[1]] == SType3 &)];
			pos4  = ListPosition[RealScalarList,_List?(#[[1]] == SType4 &)];
			If[pos1 == {} || pos2 == {} || pos3 == {} || pos4 == {},
				Message[Scalar::UnknownParticle];
				Return[];
			];
			If[BosonIndexOut[pos1[[1,1]], SList1] || BosonIndexOut[pos2[[1,1]], SList2] || BosonIndexOut[pos3[[1,1]], SList3] || BosonIndexOut[pos4[[1,1]], SList4],
				Return[0];
			];
			Return[BetaQuartic[pos1[[1,1]], pos2[[1,1]], pos3[[1,1]], pos4[[1,1]], SList1, SList2, SList3, SList4, loop]//SimplifyProduct];
		];

		(* Scalar Cubic *)
		\[Beta][SType1_, SType2_, SType3_, SList1_List, SList2_List, SList3_List, loop_] := Module[
			{pos1, pos2, pos3},
			If[MemberQ[ComplexScalarList, _?((# === SType1)&)],
				Return[Sqrt[2] \[Beta][Re[SType1], SType2, SType3, SList1, SList2, SList3, loop]];
			];
			If[MemberQ[ComplexScalarList, _?((# === SType2)&)],
				Return[Sqrt[2] \[Beta][SType1, Re[SType2], SType3, SList1, SList2, SList3, loop]];
			];
			If[MemberQ[ComplexScalarList, _?((# === SType3)&)],
				Return[Sqrt[2] \[Beta][SType1, SType2, Re[SType3], SList1, SList2, SList3, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType1)&)],
				Return[Sqrt[2] \[Beta][Re[SType1[[1]]], SType2, SType3, Join[{SList1[[2]], SList1[[1]]},SList1[[3;;]]], SList2, SList3, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType2)&)],
				Return[Sqrt[2] \[Beta][SType1, Re[SType2[[1]]], SType3, SList1, Join[{SList2[[2]], SList2[[1]]},SList2[[3;;]]], SList3, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType3)&)],
				Return[Sqrt[2] \[Beta][SType1, SType2, Re[SType3[[1]]], SList1, SList2, Join[{SList3[[2]], SList3[[1]]},SList3[[3;;]]], loop]];
			];
			pos1  = ListPosition[RealScalarList,_List?(#[[1]] == SType1 &)];
			pos2  = ListPosition[RealScalarList,_List?(#[[1]] == SType2 &)];
			pos3  = ListPosition[RealScalarList,_List?(#[[1]] == SType3 &)];
			If[pos1 == {} || pos2 == {} || pos3 == {},
				Message[Scalar::UnknownParticle];
				Return[];
			];
			If[BosonIndexOut[pos1[[1,1]], SList1] || BosonIndexOut[pos2[[1,1]], SList2] || BosonIndexOut[pos3[[1,1]], SList3],
				Return[0];
			];
			Return[BetaQuartic[pos1[[1,1]], pos2[[1,1]], pos3[[1,1]], Length[RealScalarList]+1, SList1, SList2, SList3, Function[{x}, 1]/@Range[NumberOfSubgroups+2], loop]//SimplifyProduct];
		]/;(Dimensions[SList1][[1]] == NumberOfSubgroups+2 && Dimensions[SList2][[1]] == NumberOfSubgroups+2 && Dimensions[SList3][[1]] == NumberOfSubgroups+2);

		(* Scalar Mass *)
		\[Beta][SType1_, SType2_, SList1_List, SList2_List, loop_] := Module[
			{pos1, pos2},
			If[MemberQ[ComplexScalarList, _?((# === SType1)&)],
				Return[Sqrt[2] \[Beta][Re[SType1], SType2, SList1, SList2, loop]];
			];
			If[MemberQ[ComplexScalarList, _?((# === SType2)&)],
				Return[Sqrt[2] \[Beta][SType1, Re[SType2], SList1, SList2, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType1)&)],
				Return[Sqrt[2] \[Beta][Re[SType1[[1]]], SType2, Join[{SList1[[2]], SList1[[1]]},SList1[[3;;]]], SList2, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType2)&)],
				Return[Sqrt[2] \[Beta][SType1, Re[SType2[[1]]], SList1, Join[{SList2[[2]], SList2[[1]]},SList2[[3;;]]], loop]];
			];
			pos1  = ListPosition[RealScalarList,_List?(#[[1]] == SType1 &)];
			pos2  = ListPosition[RealScalarList,_List?(#[[1]] == SType2 &)];
			If[pos1 == {} || pos2 == {},
				Message[Scalar::UnknownParticle];
				Return[];
			];
			If[BosonIndexOut[pos1[[1,1]], SList1] || BosonIndexOut[pos2[[1,1]], SList2],
				Return[0];
			];
			Return[1/2 BetaQuartic[pos1[[1,1]], pos2[[1,1]], Length[RealScalarList]+1, Length[RealScalarList]+1, SList1, SList2, Function[{x}, 1]/@Range[NumberOfSubgroups+2], Function[{x}, 1]/@Range[NumberOfSubgroups+2], loop]//SimplifyProduct];
		]/;(Dimensions[SList1][[1]] == NumberOfSubgroups+2 && Dimensions[SList2][[1]] == NumberOfSubgroups+2);

		(* Scalar Linear interaction *)
		\[Beta][SType1_, SList1_List, loop_] := Module[
			{pos1},
			If[MemberQ[ComplexScalarList, _?((# === SType1)&)],
				Return[Sqrt[2] \[Beta][Re[SType1], SList1, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType1)&)],
				Return[Sqrt[2] \[Beta][Re[SType1[[1]]], Join[{SList1[[2]], SList1[[1]]},SList1[[3;;]]], loop]];
			];
			pos1  = ListPosition[RealScalarList,_List?(#[[1]] == SType1 &)];
			If[pos1 == {},
				Message[Scalar::UnknownParticle];
				Return[];
			];
			If[BosonIndexOut[pos1[[1,1]], SList1],
				Return[0];
			];
			Return[BetaQuartic[pos1[[1,1]], Length[RealScalarList]+1, Length[RealScalarList]+1, Length[RealScalarList]+1, SList1, Function[{x}, 1]/@Range[NumberOfSubgroups+2], Function[{x}, 1]/@Range[NumberOfSubgroups+2], Function[{x}, 1]/@Range[NumberOfSubgroups+2], loop]//SimplifyProduct];
		]/;(Dimensions[SList1][[1]] == NumberOfSubgroups+2);

		(* Fermion Mass *)
		\[Beta][FType1_, FType2_, FList1_List, FList2_List, loop_ ] := Module[
			{posF1, posF2},
			posF1 = ListPosition[AdjWeylFermionList,_List?(#[[1]] == FType1 &)];
			posF2 = ListPosition[AdjWeylFermionList,_List?(#[[1]] == FType2 &)];
			If[posF1 == {} || posF2 == {},
				Message[Fermion::UnknownParticle];
				Return[];
			];
			If[FermionIndexOut[AdjWeylFermionList[[posF1[[1,1]], 2]], FList1] || FermionIndexOut[AdjWeylFermionList[[posF2[[1,1]], 2]], FList2],
				Return[0];
			];
			Return[BetaYukawa[Length[RealScalarList]+1, posF1[[1,1]], posF2[[1,1]], Function[{x}, 1]/@Range[NumberOfSubgroups+2], FList1, FList2, loop]//SimplifyProduct];
		]/;(Dimensions[FList1][[1]] == NumberOfSubgroups+1 && Dimensions[FList2][[1]] == NumberOfSubgroups+1);


		(* Interfaces for anomalous dimensions *)

		(* Fermion *)
		\[Gamma][FType1_, FType2_, FList1_List, FList2_List, loop_] := Module[
			{posF1, posF2},
			posF1 = ListPosition[AdjWeylFermionList,_List?(#[[1]] == FType1 &)];
			posF2 = ListPosition[AdjWeylFermionList,_List?(#[[1]] == FType2 &)];
			If[posF1 == {} || posF2 == {},
				Message[Fermion::UnknownParticle];
				Return[];
			];
			If[FermionIndexOut[AdjWeylFermionList[[posF1[[1,1]], 2]], FList1] || FermionIndexOut[AdjWeylFermionList[[posF2[[1,1]], 2]], FList2],
				Return[0];
			];
			Return[(FGamma[posF1[[1,1]], posF2[[1,1]], FList1, FList2, loop] + FGamma[posF2[[1,1]], posF1[[1,1]], FList2, FList1, loop])//SimplifyProduct];
		]/;(Dimensions[FList1][[1]] == NumberOfSubgroups+1 && Dimensions[FList2][[1]] == NumberOfSubgroups+1);

		(* Scalar *)
		\[Gamma][SType1_, SType2_,SList1_List, SList2_List, loop_] := Module[
			{pos1, pos2},
			If[MemberQ[ComplexScalarList, _?((# === SType1)&)],
				Return[\[Gamma][Re[SType1], SType2, SList1, SList2, loop]];
			];
			If[MemberQ[ComplexScalarList, _?((# === SType2)&)],
				Return[\[Gamma][SType1, Re[SType2], SList1, SList2, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType1)&)],
				Return[\[Gamma][Re[SType1], SType2, Join[{SList1[[2]], SList1[[1]]},SList1[3;;]], SList2, loop]];
			];
			If[MemberQ[adj/@ComplexScalarList, _?((# === SType2)&)],
				Return[\[Gamma][SType1, Re[SType2], SList1, Join[{SList2[[2]], SList2[[1]]},SList2[3;;]], loop]];
			];
			pos1  = ListPosition[RealScalarList,_List?(#[[1]] == SType1 &)];
			pos2  = ListPosition[RealScalarList,_List?(#[[1]] == SType2 &)];
			If[pos1 == {} || pos2 == {},
				Message[Scalar::UnknownParticle];
				Return[];
			];
			If[BosonIndexOut[pos1[[1,1]], SList1] || BosonIndexOut[pos2[[1,1]], SList2],
				Return[0];
			];
			Return[SGamma[pos1[[1,1]], pos2[[1,1]], SList1, SList2, loop]//SimplifyProduct];
		]/;(Dimensions[SList1][[1]] == NumberOfSubgroups+2 && Dimensions[SList2][[1]] == NumberOfSubgroups+2);

		(* Routines to zero RGEs for vertices with invalid particle indices*)

		BosonIndexOut[bos_, BList_] := (
			(NumberQ[RealScalarList[[bos,2,1]]] && NumberQ[BList[[1]]] && RealScalarList[[bos,2,1]] < BList[[1]] && IntegerQ[BList[[1]]] && BList[[1]] > 0) ||
			(NumberQ[RealScalarList[[bos,2,2]]] && NumberQ[BList[[2]]] && RealScalarList[[bos,2,2]] < BList[[2]] && IntegerQ[BList[[2]]] && BList[[2]] > 0) ||
			Or@@(Function[{x},(NumberQ[SMultiplicity[bos, x]] && NumberQ[BList[[2+x]]] && BList[[2+x]] > SMultiplicity[bos, x] && IntegerQ[BList[[2+x]]] && BList[[2+x]] > 0)]/@Range[NumberOfSubgroups])
		);

		FermionIndexOut[ferm_, FList_] := (
			(NumberQ[WeylFermionList[[ferm,2]]] && NumberQ[FList[[1]]] && WeylFermionList[[ferm,2]] < FList[[1]] && IntegerQ[FList[[1]]] && FList[[1]] > 0) ||
			Or@@(Function[{x},(NumberQ[FMultiplicity[ferm, x]] && NumberQ[FList[[1+x]]] && FList[[1+x]] > FMultiplicity[ferm, x] && IntegerQ[FList[[1+x]]] && FList[[1+x]] > 0)]/@Range[NumberOfSubgroups])
		);

		(* Backend for Beta functions *)

		BetaGauge[pos_, 0] := \[Alpha][ListGauge[[pos,1]]];

		BetaGauge[pos_, 1] := Module[
			{beta,x, ii},
			beta = 0;
			beta = beta - 22/3 Sqr[\[Alpha][ListGauge[[pos,1]]]] C2[ListGauge[[pos,1]]];
			beta = beta + 4/3 Sqr[\[Alpha][ListGauge[[pos,1]]]] Sum[S2[WeylFermionList[[ii,1]],ListGauge[[pos,1]]], {ii, 1, Length[WeylFermionList]}];
			beta = beta + 1/3 Sqr[\[Alpha][ListGauge[[pos,1]]]] Sum[S2[RealScalarList[[ii,1]], ListGauge[[pos,1]]], {ii, 1, Length[RealScalarList]}];
			Return[beta];
		];

		BetaGauge[pos_, 2] := Module[
			{beta,f,s,i},
			beta = 0;
			beta = beta - 2 Sqr[\[Alpha][ListGauge[[pos,1]]]] Sum[Y4[RealScalarList[[s,1]], ListGauge[[pos, 1]]], {s, 1, Length[RealScalarList]}]/Sqr[4 Pi];
			beta = beta - 68/3 Power[\[Alpha][ListGauge[[pos,1]]], 3] Sqr[C2[ListGauge[[pos,1]]]];
			beta = beta + Sqr[\[Alpha][ListGauge[[pos,1]]]] Sum[(Sum[4 \[Alpha][ListGauge[[i,1]]] C2[WeylFermionList[[f,1]], ListGauge[[i,1]]], {i,1,NumberOfSubgroups}] + 20/3 \[Alpha][ListGauge[[pos,1]]] C2[ListGauge[[pos,1]]])S2[WeylFermionList[[f,1]], ListGauge[[pos,1]]], {f, 1, Length[WeylFermionList]}];
			beta = beta + Sqr[\[Alpha][ListGauge[[pos,1]]]] Sum[(Sum[4 \[Alpha][ListGauge[[i,1]]] C2[RealScalarList[[s,1]], ListGauge[[i,1]]],{i,1,NumberOfSubgroups}] + 2/3 \[Alpha][ListGauge[[pos,1]]] C2[ListGauge[[pos,1]]])S2[RealScalarList[[s,1]], ListGauge[[pos,1]]], {s, 1, Length[RealScalarList]}];
			Return[beta];
		];

		BetaGauge[pos_, 3] := Module[
			{beta, f, f2, f3,f4, s, s2, SIdx, SIdx2, x},
			beta = 0;
			beta += 2 \[Alpha][ListGauge[[pos, 1]]]^2 (
				-2857/54 C2[ListGauge[[pos, 1]]]^3 \[Alpha][ListGauge[[pos, 1]]]^2
				+ Sum[
					\[Alpha][ListGauge[[pos, 1]]]^2 (
						1415/54 C2[ListGauge[[pos, 1]]]^2
						+ 205/18 C2[ListGauge[[pos, 1]]] C2[WeylFermionList[[f, 1]], ListGauge[[pos, 1]]]
						- C2[WeylFermionList[[f, 1]], ListGauge[[pos, 1]]]^2
						- Sum[
							(
								79/54 C2[ListGauge[[pos, 1]]]
								+ 11/9 C2[WeylFermionList[[f2, 1]], ListGauge[[pos, 1]]]
							) S2[WeylFermionList[[f2, 1]], ListGauge[[pos, 1]]],
							{f2, 1, Length[WeylFermionList]}
						]
					) S2[WeylFermionList[[f, 1]], ListGauge[[pos, 1]]]
					+ Sum[
						If[
							i === pos,
							0,
							\[Alpha][ListGauge[[pos, 1]]] \[Alpha][ListGauge[[i, 1]]] (
								4 C2[ListGauge[[pos, 1]]]
								- 2 C2[WeylFermionList[[f, 1]], ListGauge[[pos, 1]]]
							) +
							\[Alpha][ListGauge[[i, 1]]]^2 (
								133/18 C2[ListGauge[[i, 1]]]
								- C2[WeylFermionList[[f, 1]], ListGauge[[i, 1]]]
							) - Sum[
								If[
									j === i || j === pos,
									0,
									\[Alpha][ListGauge[[i, 1]]] \[Alpha][ListGauge[[j, 1]]] C2[WeylFermionList[[f, 1]], ListGauge[[j, 1]]]
								],
								{j, 1, NumberOfSubgroups}
							]
							- \[Alpha][ListGauge[[i, 1]]]^2 Sum[
								11/9 S2[WeylFermionList[[f2, 1]], ListGauge[[i, 1]]],
								{f2, 1, Length[WeylFermionList]}
							]
						] S2[WeylFermionList[[f, 1]], ListGauge[[pos, 1]]] C2[WeylFermionList[[f, 1]], ListGauge[[i, 1]]],
						{i, 1, NumberOfSubgroups}
					],
					{f, 1, Length[WeylFermionList]}
				]
				+ Sum[
						\[Alpha][ListGauge[[pos, 1]]]^2 (
							545/216 C2[ListGauge[[pos, 1]]]^2
							+ 1129/72 C2[ListGauge[[pos, 1]]] C2[RealScalarList[[s, 1]], ListGauge[[pos, 1]]]
							+ 29/4 C2[RealScalarList[[s, 1]], ListGauge[[pos, 1]]]^2
							+ 1/4 Sum[
								(
										1/27 C2[ListGauge[[pos, 1]]]
										- 49/18 C2[RealScalarList[[s2, 1]], ListGauge[[pos, 1]]]
								)  S2[RealScalarList[[s2, 1]], ListGauge[[pos, 1]]],
								{s2, 1, Length[RealScalarList]}
							]
						) S2[RealScalarList[[s, 1]], ListGauge[[pos, 1]]]
						+ Sum[
							If[
								i === pos,
								0,
								\[Alpha][ListGauge[[pos, 1]]] \[Alpha][ListGauge[[i, 1]]] (
									25/4 C2[ListGauge[[pos, 1]]]
									+ 29/2 C2[RealScalarList[[s, 1]], ListGauge[[pos, 1]]]
								) + \[Alpha][ListGauge[[i, 1]]]^2 (
										679/72 C2[ListGauge[[i, 1]]]
										+ 29/4 C2[RealScalarList[[s, 1]], ListGauge[[i, 1]]]
								) - Sum[
									If[
										j === i || j === pos,
										0,
										2 \[Alpha][ListGauge[[i, 1]]] \[Alpha][ListGauge[[j, 1]]] C2[RealScalarList[[s, 1]], ListGauge[[j, 1]]]
									],
									{j, 1, NumberOfSubgroups}
								] - \[Alpha][ListGauge[[i, 1]]]^2 Sum[
									49/72 S2[RealScalarList[[s2, 1]], ListGauge[[i, 1]]],
									{s2, 1, Length[RealScalarList]}
								]
							] S2[RealScalarList[[s, 1]], ListGauge[[pos, 1]]] C2[RealScalarList[[s, 1]], ListGauge[[i, 1]]],
							{i, 1, NumberOfSubgroups}
						],
					{s, 1, Length[RealScalarList]}
				]
				- Sum[
					\[Alpha][ListGauge[[pos, 1]]]^2 (
							29/54 C2[ListGauge[[pos, 1]]]
							+ 23/36 C2[WeylFermionList[[f, 1]], ListGauge[[pos, 1]]]
							+ 25/18 C2[RealScalarList[[s, 1]], ListGauge[[pos, 1]]]
					) S2[WeylFermionList[[f, 1]], ListGauge[[pos, 1]]] S2[RealScalarList[[s, 1]], ListGauge[[pos, 1]]] + Sum[
						If[
							i === pos,
							0,
							25/18 C2[RealScalarList[[s, 1]], ListGauge[[i, 1]]] S2[RealScalarList[[s, 1]], ListGauge[[pos, 1]]] S2[WeylFermionList[[f, 1]], ListGauge[[i, 1]]] \[Alpha][ListGauge[[i, 1]]]^2
							+ 23/36 C2[WeylFermionList[[f, 1]], ListGauge[[i, 1]]] S2[WeylFermionList[[f, 1]], ListGauge[[pos, 1]]] S2[RealScalarList[[s, 1]], ListGauge[[i, 1]]] \[Alpha][ListGauge[[i, 1]]]^2
						],
						{i, 1, NumberOfSubgroups}
					],
					{s, 1, Length[RealScalarList]},
					{f, 1, Length[WeylFermionList]}
				]
			);
			beta -= 6 Sum[
				(
					-3/4 C2[ListGauge[[pos,1]]] \[Alpha][ListGauge[[pos,1]]]
					+7/6 Sum[\[Alpha][ListGauge[[i,1]]] C2[RealScalarList[[s,1]], ListGauge[[i,1]]], {i, 1, NumberOfSubgroups}]
				) C2[RealScalarList[[s,1]], ListGauge[[pos,1]]] Y2[RealScalarList[[s,1]], ListGauge[[pos, 1]]]
				, {s, 1, Length[RealScalarList]}
			] Power[\[Alpha][ListGauge[[pos,1]]], 2]/Power[4 \[Pi], 2];
			beta -= 6 SimplifyProduct[(2 C2[ListGauge[[pos,1]]]) Sum[Y4[RealScalarList[[s,1]], ListGauge[[pos,1]]], {s, 1, Length[RealScalarList]}]] Power[\[Alpha][ListGauge[[pos,1]]], 3]/Power[4 \[Pi], 2];
			beta -= 6 SimplifyProduct[
				Sum[8/3 \[Alpha][ListGauge[[pos2,1]]] (
						 7/8 C2[RealScalarList[[s,1]], ListGauge[[pos2,1]]] Y4[RealScalarList[[s,1]], ListGauge[[pos,1]]]
						 + 1/8 C2[RealScalarList[[s,1]], ListGauge[[pos,1]]] Y4[RealScalarList[[s,1]], ListGauge[[pos2,1]]] d[ListGauge[[pos2, 1]]]/d[ListGauge[[pos, 1]]] 
					), 
					{pos2, 1, NumberOfSubgroups}, 
					{s, 1, Length[RealScalarList]}
				]
			] Power[\[Alpha][ListGauge[[pos,1]]], 2]/Power[4 \[Pi], 2];
			beta -= 5/2 SimplifyProduct[Sum[Y6[RealScalarList[[s,1]], ListGauge[[pos,1]], ListGauge[[pos2, 1]]] \[Alpha][ListGauge[[pos2,1]]], {s, 1, Length[RealScalarList]}, {pos2, 1, NumberOfSubgroups}]] Power[\[Alpha][ListGauge[[pos,1]]], 2] /Power[4 \[Pi], 2];
			beta -= 1/(2 d[ListGauge[[pos,1]]] Power[4 \[Pi], 2]) SimplifyProduct[Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{SIdx[1], 1, RealScalarList[[s, 2, 1]]},
								{SIdx[2], 1, RealScalarList[[s, 2, 2]]}
							},
							Function[{x}, {SIdx[2+x], 1, SMultiplicity[s, x]}]/@Range[NumberOfSubgroups]
						]
					],
					SolveTrace4[Delt[f], adj[Yuk[s]], Delt[f2], Yuk[s], Prepend[
						Function[{x}, {SIdx[2+x], SIdx[2+x], SIdx[2+x], SIdx[2+x]}]/@Range[NumberOfSubgroups],
						{SIdx[1], SIdx[2], SIdx[1], SIdx[2], SIdx[1], SIdx[2], SIdx[1], SIdx[2]}
					]]
				] Sum[
					1/2 (
						C2[WeylFermionList[[f,1]], ListGauge[[pos,1]]] C2[WeylFermionList[[f2,1]], ListGauge[[pos2,1]]] 
						+ C2[WeylFermionList[[f,1]], ListGauge[[pos2,1]]] C2[WeylFermionList[[f2,1]], ListGauge[[pos,1]]]
					)\[Alpha][ListGauge[[pos2,1]]], 
					{pos2, 1, NumberOfSubgroups}
				],
				{s, 1, Length[RealScalarList]}, {f, 1, Length[WeylFermionList]}, {f2, 1, Length[WeylFermionList]}
			] Power[\[Alpha][ListGauge[[pos,1]]], 2]];
			beta -= 6 SimplifyProduct[Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{SIdx[1], 1, RealScalarList[[s, 2, 1]]},
								{SIdx[2], 1, RealScalarList[[s, 2, 2]]},
								{SIdx2[1], 1, RealScalarList[[s2, 2, 1]]},
								{SIdx2[2], 1, RealScalarList[[s2, 2, 2]]}
							},
							Function[{x}, {SIdx[2+x], 1, SMultiplicity[s, x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {SIdx2[2+x], 1, SMultiplicity[s2, x]}]/@Range[NumberOfSubgroups]
						]
					], (
						 -1/6 SolveTrace4[Yuk[s2], adj[Yuk[s2]], Yuk[s], adj[Yuk[s]], Prepend[
							Function[{x}, {SIdx2[2+x], SIdx2[2+x], SIdx[2+x], SIdx[2+x]}]/@Range[NumberOfSubgroups],
							{SIdx2[1], SIdx2[2], SIdx2[1], SIdx2[2], SIdx[1], SIdx[2], SIdx[1], SIdx[2]}
						]] + 1/6 SolveTrace4[Yuk[s2], adj[Yuk[s]], Yuk[s2], adj[Yuk[s]], Prepend[
							Function[{x}, {SIdx2[2+x], SIdx[2+x], SIdx2[2+x], SIdx[2+x]}]/@Range[NumberOfSubgroups],
							{SIdx2[1], SIdx2[2], SIdx[1], SIdx[2], SIdx2[1], SIdx2[2], SIdx[1], SIdx[2]}
						]]  + 1/6 SolveTrace4[Yuk[s], adj[Yuk[s2]], Yuk[s], adj[Yuk[s2]], Prepend[
							Function[{x}, {SIdx[2+x], SIdx2[2+x], SIdx[2+x], SIdx2[2+x]}]/@Range[NumberOfSubgroups],
							{SIdx[1], SIdx[2], SIdx2[1], SIdx2[2], SIdx[1], SIdx[2], SIdx2[1], SIdx2[2]}
						]]
					) (C2[RealScalarList[[s,1]], ListGauge[[pos,1]]])
				],
				{s, 1, Length[RealScalarList]}, {s2, 1, Length[RealScalarList]}
			] Power[\[Alpha][ListGauge[[pos,1]]], 2]]/(d[ListGauge[[pos,1]]] Power[4 \[Pi], 4]);
			beta -= 6 SimplifyProduct[Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{SIdx[1], 1, RealScalarList[[s, 2, 1]]},
								{SIdx[2], 1, RealScalarList[[s, 2, 2]]},
								{SIdx2[1], 1, RealScalarList[[s2, 2, 1]]},
								{SIdx2[2], 1, RealScalarList[[s2, 2, 2]]}
							},
							Function[{x}, {SIdx[2+x], 1, SMultiplicity[s, x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {SIdx2[2+x], 1, SMultiplicity[s2, x]}]/@Range[NumberOfSubgroups]
						]
					],
					(
						 -1/24 SolveTrace5[Delt[f], Yuk[s2], adj[Yuk[s2]], Yuk[s], adj[Yuk[s]], Prepend[
							Function[{x}, {SIdx2[2+x], SIdx2[2+x], SIdx2[2+x], SIdx[2+x], SIdx[2+x]}]/@Range[NumberOfSubgroups],
							{SIdx2[1], SIdx2[2], SIdx2[1], SIdx2[2], SIdx2[1], SIdx2[2], SIdx[1], SIdx[2], SIdx[1], SIdx[2]}
						]] - 1/2 SolveTrace5[Delt[f], Yuk[s2], adj[Yuk[s]], Yuk[s2], adj[Yuk[s]], Prepend[
							Function[{x}, {SIdx2[2+x], SIdx2[2+x], SIdx[2+x], SIdx2[2+x], SIdx[2+x]}]/@Range[NumberOfSubgroups],
							{SIdx2[1], SIdx2[2], SIdx2[1], SIdx2[2], SIdx[1], SIdx[2], SIdx2[1], SIdx2[2], SIdx[1], SIdx[2]}
						]] - 1/8 SolveTrace5[Delt[f], adj[Yuk[s]], Yuk[s2], adj[Yuk[s2]], Yuk[s], Prepend[
							Function[{x}, {SIdx[2+x], SIdx[2+x], SIdx2[2+x], SIdx2[2+x], SIdx[2+x]}]/@Range[NumberOfSubgroups],
							{SIdx[1], SIdx[2], SIdx[1], SIdx[2], SIdx2[1], SIdx2[2], SIdx2[1], SIdx2[2], SIdx[1], SIdx[2]}
						]]
					) (C2[WeylFermionList[[f,1]], ListGauge[[pos, 1]]])
				],
				{s, 1, Length[RealScalarList]}, {s2, 1, Length[RealScalarList]}, {f, 1, Length[WeylFermionList]}
			] Power[\[Alpha][ListGauge[[pos,1]]], 2]]/(d[ListGauge[[pos,1]]] Power[4 \[Pi], 4]);
			beta += 7/(4 d[ListGauge[[pos,1]]] Power[4 \[Pi], 4]) SimplifyProduct[Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{SIdx[1], 1, RealScalarList[[s, 2, 1]]},
								{SIdx[2], 1, RealScalarList[[s, 2, 2]]},
								{SIdx2[1], 1, RealScalarList[[s2, 2, 1]]},
								{SIdx2[2], 1, RealScalarList[[s2, 2, 2]]}
							},
							Function[{x}, {SIdx[2+x], 1, SMultiplicity[s, x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {SIdx2[2+x], 1, SMultiplicity[s2, x]}]/@Range[NumberOfSubgroups]
						]
					],
					SolveTrace2[Yuk[s], adj[Yuk[s2]], Prepend[
						Function[{x}, {SIdx[2+x], SIdx2[2+x]}]/@Range[NumberOfSubgroups],
						{SIdx[1], SIdx[2], SIdx2[1], SIdx2[2]}
					]](
						SolveTrace3[Delt[f], adj[Yuk[s2]], Yuk[s], Prepend[
						Function[{x}, {SIdx2[2+x], SIdx2[2+x], SIdx[2+x]}]/@Range[NumberOfSubgroups],
						{SIdx2[1], SIdx2[2], SIdx2[1], SIdx2[2], SIdx[1], SIdx[2]}
						]] +
						SolveTrace3[Delt[f], Yuk[s2], adj[Yuk[s]], Prepend[
						Function[{x}, {SIdx2[2+x], SIdx2[2+x], SIdx[2+x]}]/@Range[NumberOfSubgroups],
						{SIdx2[1], SIdx2[2], SIdx2[1], SIdx2[2], SIdx[1], SIdx[2]}
						]]
					)  C2[WeylFermionList[[f,1]], ListGauge[[pos,1]]]
				],
				{s, 1, Length[RealScalarList]}, {s2, 1, Length[RealScalarList]}, {f, 1, Length[WeylFermionList]}
			] Power[\[Alpha][ListGauge[[pos,1]]], 2]];
			beta += -1/(4 d[ListGauge[[pos,1]]] Power[4 \[Pi], 4]) SimplifyProduct[Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{SIdx[1], 1, RealScalarList[[s, 2, 1]]},
								{SIdx[2], 1, RealScalarList[[s, 2, 2]]},
								{SIdx2[1], 1, RealScalarList[[s2, 2, 1]]},
								{SIdx2[2], 1, RealScalarList[[s2, 2, 2]]}
							},
							Function[{x}, {SIdx[2+x], 1, SMultiplicity[s, x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {SIdx2[2+x], 1, SMultiplicity[s2, x]}]/@Range[NumberOfSubgroups]
						]
					],
					SolveTrace2[Yuk[s], adj[Yuk[s2]], Prepend[
						Function[{x}, {SIdx[2+x], SIdx2[2+x]}]/@Range[NumberOfSubgroups],
						{SIdx[1], SIdx[2], SIdx2[1], SIdx2[2]}
					]](
						SolveTrace2[Yuk[s2], adj[Yuk[s]], Prepend[
							Function[{x}, {SIdx2[2+x], SIdx[2+x]}]/@Range[NumberOfSubgroups],
							{SIdx2[1], SIdx2[2], SIdx[1], SIdx[2]}
						]] +
						SolveTrace2[adj[Yuk[s2]], Yuk[s], Prepend[
							Function[{x}, {SIdx2[2+x], SIdx[2+x]}]/@Range[NumberOfSubgroups],
							{SIdx2[1], SIdx2[2], SIdx[1], SIdx[2]}
						]]
					) C2[RealScalarList[[s,1]], ListGauge[[pos,1]]]
				],
				{s, 1, Length[RealScalarList]}, {s2, 1, Length[RealScalarList]}
			] Power[\[Alpha][ListGauge[[pos,1]]], 2]];
			beta += -1/12 (\[CapitalLambda]G2[pos] //. subScalarInvariants)/Power[4 \[Pi], 4];
			beta += 6 Power[\[Alpha][ListGauge[[pos,1]]], 2]/(6 d[ListGauge[[pos,1]]] Power[4 \[Pi], 2]) ( Sum[\[Alpha][ListGauge[[pos2,1]]] \[Lambda]\[CapitalLambda]2[pos, pos2], {pos2, 1, NumberOfSubgroups}] //. subScalarInvariants);
			beta += 6 Sqr[\[Alpha][ListGauge[[pos,1]]]]/(3 d[ListGauge[[pos,1]]] Power[4 \[Pi], 4]) Sum[
				ContractSum[
					ReleaseHold[tr[adj[Yuk[s]][AdjWeylFermionList[[f,3]], f2], Yuk[s2][AdjWeylFermionList[[f2,3]], f3], adj[Yuk[s2]][AdjWeylFermionList[[f3,3]], f4], Yuk[s][AdjWeylFermionList[[f4,3]], f]] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk1 //.subProd]//.subYuk2 /.{
						tr[y1_, y2_, y3_, y4_]:>(
							(
								Refine[
									GetGenTrace[{y1, y2, y3, y4}, {{sIdx[1], sIdx[2]}, {sIdx2[1], sIdx2[2]}, {sIdx2[1], sIdx2[2]}, {sIdx[1], sIdx[2]}}]//.subProd
								]
							)(
								Refine[ContractSum @@ Join[
									{
										(	
											Times @@ Function[ 
												x,
												y1[[1+x,1]][sIdx[2+x], ff1[x], ff2[x]] y2[[1+x,1]][sIdx2[2+x], ff2[x], ff3[x]] y3[[1+x,1]][sIdx2[2+x], ff34[x], ff4[x]] y4[[1+x,1]][sIdx[2+x], ff4[x], ff5[x]] 
											] /@ Range[NumberOfSubgroups]
										)(
											\[CapitalLambda][pos][Join[{AdjWeylFermionList[[f,3]], 1}, ff5 /@ Range[NumberOfSubgroups]], Join[{AdjWeylFermionList[[f3,3]], 1}, ff3 /@ Range[NumberOfSubgroups]], Join[{f, 1}, ff1 /@ Range[NumberOfSubgroups]], Join[{f3, 1}, ff34 /@ Range[NumberOfSubgroups]]] 
										) //. sub\[CapitalLambda]F 
									},
									Function[x, {ff1[x], 1, FMultiplicity[AdjWeylFermionList[[f, 2]], x]}] /@ Range[NumberOfSubgroups],
									Function[x, {ff2[x], 1, FMultiplicity[AdjWeylFermionList[[f2, 2]], x]}] /@ Range[NumberOfSubgroups],
									Function[x, {ff3[x], 1, FMultiplicity[AdjWeylFermionList[[f3, 2]], x]}] /@ Range[NumberOfSubgroups],
									Function[x, {ff34[x], 1, FMultiplicity[AdjWeylFermionList[[f3, 2]], x]}] /@ Range[NumberOfSubgroups],
									Function[x, {ff4[x], 1, FMultiplicity[AdjWeylFermionList[[f4, 2]], x]}] /@ Range[NumberOfSubgroups],
									Function[x, {ff5[x], 1, FMultiplicity[AdjWeylFermionList[[f, 2]], x]}] /@ Range[NumberOfSubgroups],
									Function[x, {sIdx[2+x], 1, SMultiplicity[s, x]}] /@ Range[NumberOfSubgroups],
									Function[x, {sIdx2[2+x], 1, SMultiplicity[s2, x]}] /@ Range[NumberOfSubgroups]
								]]
							)
						)
					},
					{sIdx[1], 1, RealScalarList[[s, 2, 1]]},
					{sIdx[2], 1, RealScalarList[[s, 2, 2]]},
					{sIdx2[1], 1, RealScalarList[[s2, 2, 1]]},
					{sIdx2[2], 1, RealScalarList[[s2, 2, 2]]}
				],
				{f, 1, Length[AdjWeylFermionList]},
				{f2, 1, Length[AdjWeylFermionList]},
				{f3, 1, Length[AdjWeylFermionList]},
				{f4, 1, Length[AdjWeylFermionList]},
				{s, 1, Length[RealScalarList]},
				{s2, 1, Length[RealScalarList]}
			];
			Return[beta];
		];

		BetaYukawa[pa_, pi_, pj_, la_, li_, lj_, 0] := ReleaseHold[Yuk[pa][pi,pj] /. subYuk1]/.{
			transpose[yuk[a_]]:>(If[(MatchQ[ListYukawa[[a,6]], Mat[___]] || MatchQ[ListYukawa[[a,6]], Conjugate[Mat[___]]] || MatchQ[ListYukawa[[a,6]], aa_ Mat[___]] || MatchQ[ListYukawa[[a,6]], aa_ Conjugate[Mat[___]]]  || MatchQ[ListYukawa[[a,6]], Mat[___]&] || MatchQ[ListYukawa[[a,6]], Conjugate[Mat[___]]&]  || MatchQ[ListYukawa[[a,6]], aa_ Mat[___]&] || MatchQ[ListYukawa[[a,6]], aa_ Conjugate[Mat[___]]&]), transpose[ListYukawa[[a, 1]]][lj[[1]], li[[1]]], ListYukawa[[a, 1]]] Refine[ListYukawa[[a,6]][la[[1]], la[[2]], lj[[1]], li[[1]]]/.{Mat:>Identity}] Times@@(Function[{x}, Refine[Conjugate[ListYukawa[[a,5,x]][la[[2+x]], lj[[1+x]], li[[1+x]]]]]]/@Range[NumberOfSubgroups])),
			yuk[a_]:>(If[(MatchQ[ListYukawa[[a,6]], Mat[___]] || MatchQ[ListYukawa[[a,6]], Conjugate[Mat[___]]] || MatchQ[ListYukawa[[a,6]], aa_ Mat[___]] || MatchQ[ListYukawa[[a,6]], aa_ Conjugate[Mat[___]]]  || MatchQ[ListYukawa[[a,6]], Mat[___]&] || MatchQ[ListYukawa[[a,6]], Conjugate[Mat[___]]&]  || MatchQ[ListYukawa[[a,6]], aa_ Mat[___]&] || MatchQ[ListYukawa[[a,6]], aa_ Conjugate[Mat[___]]&]), ListYukawa[[a, 1]][li[[1]], lj[[1]]], ListYukawa[[a, 1]]] (ListYukawa[[a,6]][la[[1]], la[[2]], li[[1]], lj[[1]]]/.{Mat:>Identity}) Times@@(Function[{x}, ListYukawa[[a,5,x]][la[[2+x]], li[[1+x]], lj[[1+x]]]]/@Range[NumberOfSubgroups]))
		};

		BetaYukawa[pa_, pi_, pj_, la_, li_, lj_, 1] := Module[
			{beta, ss1, ii, x, x2, x3, sumIdx, assHold},
			assHold=$Assumptions;
			$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)]/@Range[NumberOfSubgroups+2];
			beta = 0;
			beta += 1/2  Sum[
				ContractSum@@Join[
					{
						SolveProd3[Yuk[ss1[0]], adj[Yuk[ss1[0]]], Yuk[pa], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss1[2+x2], ss1[2+x2], la[[2+x2]]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], ss1[1], ss1[2], la[[1]], la[[2]]}]],
						{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
						{ss1[2], 1, RealScalarList[[ss1[0],2,2]]}
					},
					Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
				],
				{ss1[0], 1, Length[RealScalarList]}
			];
			beta += 1/2 Sum[
				ContractSum@@Join[
					{
						SolveProd3[Yuk[pa], adj[Yuk[ss1[0]]], Yuk[ss1[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {la[[2+x2]], ss1[2+x2], ss1[2+x2]}]/@Range[NumberOfSubgroups], {la[[1]], la[[2]], ss1[1], ss1[2], ss1[1], ss1[2]}]],
						{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
						{ss1[2], 1, RealScalarList[[ss1[0],2,2]]}
					},
					Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
				],
				{ss1[0], 1, Length[RealScalarList]}
			];
			beta += 2  Sum[
				ContractSum@@Join[
					{
						SolveProd3[Yuk[ss1[0]], adj[Yuk[pa]], Yuk[ss1[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss1[2+x2], la[[2+x2]], ss1[2+x2]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], la[[1]], la[[2]], ss1[1], ss1[2]}]],
						{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
						{ss1[2], 1, RealScalarList[[ss1[0],2,2]]}
					},
					Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
				],
				{ss1[0], 1, Length[RealScalarList]}
			];
			If[pa <= Length[RealScalarList],
				beta = beta + 1/2 Sum[
					ContractSum@@Join[
						{
							(
								SolveTrace2[Yuk[pa], adj[Yuk[ss1[0]]], Prepend[Function[{x}, {la[[2+x]], ss1[2+x]}]/@Range[NumberOfSubgroups], {la[[1]], la[[2]], ss1[1], ss1[2]}]] +
								SolveTrace2[adj[Yuk[pa]], Yuk[ss1[0]], Prepend[Function[{x}, {la[[2+x]], ss1[2+x]}]/@Range[NumberOfSubgroups], {la[[1]], la[[2]], ss1[1], ss1[2]}]]
							) BetaYukawa[ss1[0], pi, pj, ss1/@Range[NumberOfSubgroups+2], li, lj, 0],
							{ss1[1], 1, RealScalarList[[ss1[0], 2, 1]]},
							{ss1[2], 1, RealScalarList[[ss1[0], 2, 2]]}
						}, Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
					],
					{ss1[0], 1, Length[RealScalarList]}
				]/.{tr[adj[a_],b_]:>tr[b,adj[a]]};
			];
			beta -= 3 Sum[Sqr[ListGauge[[ii,1]]](C2[WeylFermionList[[AdjWeylFermionList[[pi,2]],1]], ListGauge[[ii,1]]] + C2[WeylFermionList[[AdjWeylFermionList[[pj,2]],1]], ListGauge[[ii,1]]]) BetaYukawa[pa, pi, pj, la, li, lj, 0], {ii, 1, NumberOfSubgroups}];
			$Assumptions=assHold;
			Return[beta/Sqr[4\[Pi]]];
		];

		BetaYukawa[pa_, pi_, pj_, la_, li_, lj_, 2] := Module[
			{beta, fHold, ssb, ssc, ss, ss1, ss2, ss3, ff, ii, ii2, x, x2, assHold},
			assHold = $Assumptions;
			$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)&&Element[ss3[x],Integers]&&(ss3[x]>0)&&Element[ss[x],Integers]&&(ss[x]>0)]/@Range[NumberOfSubgroups+2];
			beta = 0;
			beta += 2 Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0],2,2]]},
								{ss2[1], 1, RealScalarList[[ss2[0],2,1]]},
								{ss2[2], 1, RealScalarList[[ss2[0],2,2]]}
							},
							Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[2+x], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
						]
					],
					SolveProd5[Yuk[ss1[0]], adj[Yuk[ss2[0]]], Yuk[pa], adj[Yuk[ss1[0]]], Yuk[ss2[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss1[2+x2], ss2[2+x2], la[[2+x2]], ss1[2+x2], ss2[2+x2]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], ss2[1], ss2[2], la[[1]], la[[2]], ss1[1], ss1[2], ss2[1], ss2[2]}]]
				],
				{ss1[0], 1, Length[RealScalarList]},
				{ss2[0], 1, Length[RealScalarList]}
			];
			beta -= 2 Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0],2,2]]},
								{ss2[1], 1, RealScalarList[[ss2[0],2,1]]},
								{ss2[2], 1, RealScalarList[[ss2[0],2,2]]}
							},
							Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[2+x], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
						]
					],
					SolveProd5[Yuk[ss1[0]], adj[Yuk[ss2[0]]], Yuk[pa], adj[Yuk[ss2[0]]], Yuk[ss1[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss1[2+x2], ss2[2+x2], la[[2+x2]], ss2[2+x2], ss1[2+x2]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], ss2[1], ss2[2], la[[1]], la[[2]], ss2[1], ss2[2], ss1[1], ss1[2]}]]
				],
				{ss1[0], 1, Length[RealScalarList]},
				{ss2[0], 1, Length[RealScalarList]}
			];
			beta -= Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0],2,2]]},
								{ss2[1], 1, RealScalarList[[ss2[0],2,1]]},
								{ss2[2], 1, RealScalarList[[ss2[0],2,2]]}
							},
							Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[2+x], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
						]
					],
					SolveProd5[Yuk[ss1[0]], adj[Yuk[ss2[0]]], Yuk[ss2[0]], adj[Yuk[pa]], Yuk[ss1[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss1[2+x2], ss2[2+x2], ss2[2+x2], la[[2+x2]], ss1[2+x2]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], ss2[1], ss2[2], ss2[1], ss2[2], la[[1]], la[[2]], ss1[1], ss1[2]}]]
				],
				{ss1[0], 1, Length[RealScalarList]},
				{ss2[0], 1, Length[RealScalarList]}
			];
			beta -= Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0],2,2]]},
								{ss2[1], 1, RealScalarList[[ss2[0],2,1]]},
								{ss2[2], 1, RealScalarList[[ss2[0],2,2]]}
							},
							Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[2+x], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
						]
					],
					SolveProd5[Yuk[ss1[0]], adj[Yuk[pa]], Yuk[ss2[0]], adj[Yuk[ss2[0]]], Yuk[ss1[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss1[2+x2], la[[2+x2]], ss2[2+x2], ss2[2+x2], ss1[2+x2]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], la[[1]], la[[2]], ss2[1], ss2[2], ss2[1], ss2[2], ss1[1], ss1[2]}]]
				],
				{ss1[0], 1, Length[RealScalarList]},
				{ss2[0], 1, Length[RealScalarList]}
			];
			beta -= 1/8 Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0],2,2]]},
								{ss2[1], 1, RealScalarList[[ss2[0],2,1]]},
								{ss2[2], 1, RealScalarList[[ss2[0],2,2]]}
							},
							Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[2+x], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
						]
					],
					SolveProd5[Yuk[ss1[0]], adj[Yuk[ss2[0]]], Yuk[ss2[0]], adj[Yuk[ss1[0]]], Yuk[pa], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss1[2+x2], ss2[2+x2], ss2[2+x2], ss1[2+x2], la[[2+x2]]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], ss2[1], ss2[2], ss2[1], ss2[2], ss1[1], ss1[2], la[[1]], la[[2]]}]]
				],
				{ss1[0], 1, Length[RealScalarList]},
				{ss2[0], 1, Length[RealScalarList]}
			];
			beta -= 1/8 Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0],2,2]]},
								{ss2[1], 1, RealScalarList[[ss2[0],2,1]]},
								{ss2[2], 1, RealScalarList[[ss2[0],2,2]]}
							},
							Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[2+x], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
						]
					],
					SolveProd5[Yuk[pa], adj[Yuk[ss1[0]]], Yuk[ss2[0]], adj[Yuk[ss2[0]]], Yuk[ss1[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {la[[2+x2]], ss1[2+x2], ss2[2+x2], ss2[2+x2], ss1[2+x2]}]/@Range[NumberOfSubgroups], {la[[1]], la[[2]], ss1[1], ss1[2], ss2[1], ss2[2], ss2[1], ss2[2], ss1[1], ss1[2]}]]
				],
				{ss1[0], 1, Length[RealScalarList]},
				{ss2[0], 1, Length[RealScalarList]}
			];
			beta -= 2 Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]},
								{ss2[1], 1, RealScalarList[[ss2[0], 2,1]]},
								{ss2[2], 1, RealScalarList[[ss2[0], 2,2]]}
							},
							Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
						]
					],
					(Y2S[Prepend[la, pa], ss1/@Range[0, NumberOfSubgroups+2]]//.subScalarInvariants) SolveProd3[Yuk[ss2[0]], adj[Yuk[ss1[0]]], Yuk[ss2[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss2[2+x2], ss1[2+x2], ss2[2+x2]}]/@Range[NumberOfSubgroups], {ss2[1], ss2[2], ss1[1], ss1[2], ss2[1], ss2[2]}]]
				], 
				{ss1[0], 1, Length[RealScalarList]}, {ss2[0], 1, Length[RealScalarList]}];
			If[pa <= Length[RealScalarList],
				beta -= Hbar2SY[Prepend[la, pa], Prepend[li, pi], Prepend[lj, pj]]//.subScalarInvariants;
				beta -= 3/2 H2SY[Prepend[la, pa], Prepend[li, pi], Prepend[lj, pj]]//.subScalarInvariants;
				beta += 1/2 \[CapitalLambda]2SY[Prepend[la, pa], Prepend[li, pi], Prepend[lj, pj]]//.subScalarInvariants;
			];
			beta -= 3/4 Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{ss[1], 1, RealScalarList[[ss[0], 2,1]]},
								{ss[2], 1, RealScalarList[[ss[0], 2,2]]},
								{ss2[1], 1, RealScalarList[[ss2[0], 2,1]]},
								{ss2[2], 1, RealScalarList[[ss2[0], 2,2]]}
							},
							Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
						]
					], (
						Y2S[ss/@Range[0, NumberOfSubgroups+2], ss2/@Range[0, NumberOfSubgroups+2]]//.subScalarInvariants) (
						SolveProd3[Yuk[ss[0]], adj[Yuk[ss2[0]]], Yuk[pa], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss[2+x2], ss2[2+x2], la[[2+x2]]}]/@Range[NumberOfSubgroups], {ss[1], ss[2], ss2[1], ss2[2], la[[1]], la[[2]]}]] +
						SolveProd3[Yuk[pa], adj[Yuk[ss[0]]], Yuk[ss2[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {la[[2+x2]], ss[2+x2], ss2[2+x2]}]/@Range[NumberOfSubgroups], {la[[1]], la[[2]], ss[1], ss[2], ss2[1], ss2[2]}]]
					)
				], 
				{ss[0], 1, Length[RealScalarList]}, {ss2[0], 1, Length[RealScalarList]}
			];
			beta -= 2 Sum[
				ApplyDistribute[
					Function[contr,
						ContractSum@@Join[
							{
								contr,
								{ss[1], 1, RealScalarList[[ss[0], 2,1]]},
								{ss2[1], 1, RealScalarList[[ss2[0], 2,1]]},
								{ss3[1], 1, RealScalarList[[ss3[0], 2,1]]},
								{ss[2], 1, RealScalarList[[ss[0], 2,2]]},
								{ss2[2], 1, RealScalarList[[ss2[0], 2,2]]},
								{ss3[2], 1, RealScalarList[[ss3[0], 2,2]]}
							},
							Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss3[x+2], 1, SMultiplicity[ss3[0], x]}]/@Range[NumberOfSubgroups]
						]
					],
					24 BetaQuartic[pa, ss[0], ss2[0], ss3[0], la, ss/@Range[NumberOfSubgroups+2], ss2/@Range[NumberOfSubgroups+2], ss3/@Range[NumberOfSubgroups+2],0] SolveProd3[Yuk[ss[0]], adj[Yuk[ss2[0]]], Yuk[ss3[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss[2+x2], ss2[2+x2], ss3[2+x2]}]/@Range[NumberOfSubgroups], {ss[1], ss[2], ss2[1], ss2[2], ss3[1], ss3[2]}]]
				], 
				{ss[0], 1, Length[RealScalarList]}, {ss2[0], 1, Length[RealScalarList]}, {ss3[0], 1, Length[RealScalarList]}
			];
			beta += Sum[
				Sum[
					Sqr[ListGauge[[ii,1]]](
						3 C2[WeylFermionList[[AdjWeylFermionList[[pi,2]],1]], ListGauge[[ii,1]]] +
						3 C2[WeylFermionList[[AdjWeylFermionList[[pj,2]],1]], ListGauge[[ii,1]]] +
						6 C2[RealScalarList[[ss[0], 1]], ListGauge[[ii,1]]] -
						12 If[pa > Length[RealScalarList], 0, C2[RealScalarList[[pa,1]], ListGauge[[ii,1]]]]
					), {ii, 1, NumberOfSubgroups}
				] ApplyDistribute[Function[contr, ContractSum@@Join[
					{
						contr,
						{ss[1], 1, RealScalarList[[ss[0],2,1]]},
						{ss[2], 1, RealScalarList[[ss[0],2,2]]}
					},
					Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0],x]}]/@Range[NumberOfSubgroups]
				]], SolveProd3[
					Yuk[ss[0]], adj[Yuk[pa]], Yuk[ss[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss[2+x2], la[[2+x2]], ss[2+x2]}]/@Range[NumberOfSubgroups], {ss[1], ss[2], la[[1]], la[[2]], ss[1], ss[2]}]
				]] + Sum[
					Sqr[ListGauge[[ii,1]]](
						-7/4 C2[WeylFermionList[[AdjWeylFermionList[[pi,2]],1]], ListGauge[[ii,1]]] +
						9/2 C2[RealScalarList[[ss[0],1]],ListGauge[[ii,1]]]
					),
					{ii, 1, NumberOfSubgroups}
				] ApplyDistribute[Function[contr, ContractSum@@Join[
					{
						contr,
						{ss[1], 1, RealScalarList[[ss[0],2,1]]},
						{ss[2], 1, RealScalarList[[ss[0],2,2]]}
					},
					Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0],x]}]/@Range[NumberOfSubgroups]
				]], SolveProd3[
					Yuk[ss[0]], adj[Yuk[ss[0]]], Yuk[pa], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss[2+x2], ss[2+x2], la[[2+x2]]}]/@Range[NumberOfSubgroups], {ss[1], ss[2], ss[1], ss[2], la[[1]], la[[2]]}]
				]] + Sum[
					Sqr[ListGauge[[ii,1]]](
						-7/4 C2[WeylFermionList[[AdjWeylFermionList[[pj,2]],1]], ListGauge[[ii,1]]] +
						9/2 C2[RealScalarList[[ss[0],1]],ListGauge[[ii,1]]]
					),
					{ii, 1, NumberOfSubgroups}
				] ApplyDistribute[Function[contr, ContractSum@@Join[
					{
						contr,
						{ss[1], 1, RealScalarList[[ss[0],2,1]]},
						{ss[2], 1, RealScalarList[[ss[0],2,2]]}
					},
					Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0],x]}]/@Range[NumberOfSubgroups]
				]], SolveProd3[
					Yuk[pa], adj[Yuk[ss[0]]], Yuk[ss[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {la[[2+x2]], ss[2+x2], ss[2+x2]}]/@Range[NumberOfSubgroups], {la[[1]], la[[2]], ss[1], ss[2], ss[1], ss[2]}]
				]],
				{ss[0], 1, Length[RealScalarList]}
			];
			For[ff=1, ff<=Length[WeylFermionList], ff++,
				fHold[ff] = Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss[1], 1, RealScalarList[[ss[0],2,1]]},
									{ss[2], 1, RealScalarList[[ss[0],2,2]]}
								},
								Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0],x]}]/@Range[NumberOfSubgroups]
							]
						],
						5 SolveProd4[
							Yuk[ss[0]], Delt[ff], adj[Yuk[pa]], Yuk[ss[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss[2+x2], ss[2+x2], la[[2+x2]], ss[2+x2]}]/@Range[NumberOfSubgroups], {ss[1], ss[2], ss[1], ss[2], la[[1]], la[[2]], ss[1], ss[2]}]
						] +
						5 SolveProd4[
							Yuk[ss[0]], adj[Yuk[pa]], Delt[ff], Yuk[ss[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss[2+x2], la[[2+x2]], ss[2+x2], ss[2+x2]}]/@Range[NumberOfSubgroups], {ss[1], ss[2], la[[1]], la[[2]],  ss[1], ss[2], ss[1], ss[2]}]
						] -
						1/4 SolveProd4[
							Yuk[ss[0]], Delt[ff], adj[Yuk[ss[0]]], Yuk[pa], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss[2+x2], ss[2+x2], ss[2+x2], la[[2+x2]]}]/@Range[NumberOfSubgroups], {ss[1], ss[2], ss[1], ss[2], ss[1], ss[2], la[[1]], la[[2]]}]
						] -
						1/4 SolveProd4[
							Yuk[pa], adj[Yuk[ss[0]]], Delt[ff], Yuk[ss[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {la[[2+x2]], ss[2+x2], ss[2+x2], ss[2+x2]}]/@Range[NumberOfSubgroups], {la[[1]], la[[2]], ss[1], ss[2], ss[1], ss[2], ss[1], ss[2]}]
						]
					],
					{ss[0], 1, Length[RealScalarList]}
				];
			];
			beta += Sum[
				Sqr[ListGauge[[ii,1]]] C2[WeylFermionList[[ff,1]], ListGauge[[ii,1]]] fHold[ff],
				{ff, 1, Length[WeylFermionList]},
				{ii, 1, NumberOfSubgroups}
			];
			beta += Sum[ 6 Sqr[ListGauge[[ii,1]]] H2t[ii, Prepend[la, pa], Prepend[li, pi], Prepend[lj, pj]] //.subScalarInvariants, {ii, 1, NumberOfSubgroups}];
			beta += If[pa > Length[RealScalarList], 0, Y2FSY[pa, pi, pj, la, li, lj]//.subScalarInvariants];
			beta -= 3/2 Sum[
				Sqr[ListGauge[[ii,1]] ListGauge[[ii2,1]]] BetaYukawa[pa, pi, pj, la, li, lj, 0] (C2[WeylFermionList[[AdjWeylFermionList[[pi,2]],1]], ListGauge[[ii,1]]] C2[WeylFermionList[[AdjWeylFermionList[[pi,2]],1]], ListGauge[[ii2,1]]] + C2[WeylFermionList[[AdjWeylFermionList[[pj,2]],1]], ListGauge[[ii,1]]] C2[WeylFermionList[[AdjWeylFermionList[[pj,2]],1]], ListGauge[[ii2,1]]]),
				{ii, 1, NumberOfSubgroups},
				{ii2, 1, NumberOfSubgroups}
			];
			beta += 6 Sum[
				Sqr[ListGauge[[ii, 1]] ListGauge[[ii2, 1]]] If[pa > Length[RealScalarList], 0, C2[RealScalarList[[pa,1]], ListGauge[[ii,1]]]]  BetaYukawa[pa, pi, pj, la, li, lj, 0] (C2[WeylFermionList[[AdjWeylFermionList[[pi,2]],1]], ListGauge[[ii2,1]]] + C2[WeylFermionList[[AdjWeylFermionList[[pj,2]],1]], ListGauge[[ii2,1]]]),
				{ii, 1, NumberOfSubgroups},
				{ii2, 1, NumberOfSubgroups}
			];
			beta += Sum[
				Power[ListGauge[[ii,1]],4](
					-97/6 C2[ListGauge[[ii,1]]] +
					5/3 Sum[S2[WeylFermionList[[ff,1]], ListGauge[[ii,1]]], {ff, 1, Length[WeylFermionList]}] +
					11/12 Sum[S2[RealScalarList[[ssb,1]], ListGauge[[ii,1]]], {ssb, 1, Length[RealScalarList]}]
				) BetaYukawa[pa, pi, pj, la, li, lj, 0] (C2[WeylFermionList[[AdjWeylFermionList[[pi,2]],1]], ListGauge[[ii, 1]]] + C2[WeylFermionList[[AdjWeylFermionList[[pj,2]],1]], ListGauge[[ii, 1]]]),
				{ii, 1, NumberOfSubgroups}
			];
			beta -= 21/2 Sum[
				Sqr[ListGauge[[ii,1]] ListGauge[[ii2,1]]] If[pa > Length[RealScalarList], 0, C2[RealScalarList[[pa,1]], ListGauge[[ii,1]]] C2[RealScalarList[[pa,1]], ListGauge[[ii2,1]]]] BetaYukawa[pa, pi, pj, la, li, lj, 0],
				{ii, 1, NumberOfSubgroups},
				{ii2, 1, NumberOfSubgroups}
			];
			beta += Sum[
				Power[ListGauge[[ii,1]],4](
					49/4 C2[ListGauge[[ii,1]]] -
					1/4 Sum[S2[RealScalarList[[ssb,1]], ListGauge[[ii,1]]], {ssb, 1, Length[RealScalarList]}] -
					Sum[S2[WeylFermionList[[ff, 1]], ListGauge[[ii,1]]] ,{ff, 1, Length[WeylFermionList]}]
				) If[pa > Length[RealScalarList], 0, C2[RealScalarList[[pa,1]], ListGauge[[ii,1]]]]  BetaYukawa[pa, pi, pj, la, li, lj, 0],
				{ii, 1, NumberOfSubgroups}
			];
			$Assumptions=assHold;
			Return[beta/Power[4\[Pi], 4]];
		];


		BetaQuartic[a_, b_, c_, d_, la_, lb_, lc_, ld_, 0] := Module[
			{q},
			Return[
				ReleaseHold[(Quartic[a,b,c,d]/.subQuart1)]//.{
				Quart[q_]:>((ListQuarticSym[[q,1]] ListQuarticSym[[q,7]][la[[1]], la[[2]], lb[[1]], lb[[2]], lc[[1]], lc[[2]], ld[[1]], ld[[2]]])(Times@@(Function[{x},ListQuarticSym[[q,6,x]][la[[2+x]], lb[[2+x]], lc[[2+x]], ld[[2+x]]]]/@Range[NumberOfSubgroups])))}
			];
		];


		BetaQuartic[pa_, pb_, pc_, pd_, la_, lb_, lc_, ld_, 1] := Module[
			{beta, ss, ii, x, ii2},
			beta = 0;
			beta += Sqr[24] (
				\[CapitalLambda]2[Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]] +
				\[CapitalLambda]2[Join[{pa}, la], Join[{pc}, lc], Join[{pb}, lb], Join[{pd}, ld]] +
				\[CapitalLambda]2[Join[{pa}, la], Join[{pd}, ld], Join[{pc}, lc], Join[{pb}, lb]]
			)//.subScalarInvariants;
			beta -= 2 (
				H[Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]] +
				H[Join[{pa}, la], Join[{pb}, lb], Join[{pd}, ld], Join[{pc}, lc]] +
				H[Join[{pa}, la], Join[{pc}, lc], Join[{pb}, lb], Join[{pd}, ld]] +
				H[Join[{pa}, la], Join[{pc}, lc], Join[{pd}, ld], Join[{pb}, lb]] +
				H[Join[{pa}, la], Join[{pd}, ld], Join[{pb}, lb], Join[{pc}, lc]] +
				H[Join[{pa}, la], Join[{pd}, ld], Join[{pc}, lc], Join[{pb}, lb]] +
				H[Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld], Join[{pa}, la]] +
				H[Join[{pb}, lb], Join[{pd}, ld], Join[{pc}, lc], Join[{pa}, la]] +
				H[Join[{pc}, lc], Join[{pb}, lb], Join[{pd}, ld], Join[{pa}, la]] +
				H[Join[{pc}, lc], Join[{pd}, ld], Join[{pb}, lb], Join[{pa}, la]] +
				H[Join[{pd}, ld], Join[{pb}, lb], Join[{pc}, lc], Join[{pa}, la]] +
				H[Join[{pd}, ld], Join[{pc}, lc], Join[{pb}, lb], Join[{pa}, la]]
			)//.subScalarInvariants//.{tr[adj[a_], b_, adj[c_], d_]:>tr[b, adj[c], d, adj[a]]};
			beta += 24 (
				If[pa > Length[RealScalarList], 0,  \[CapitalLambda]Y[Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]]] +
				If[pb > Length[RealScalarList], 0,  \[CapitalLambda]Y[Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld], Join[{pa}, la]]] +
				If[pc > Length[RealScalarList], 0,  \[CapitalLambda]Y[Join[{pc}, lc], Join[{pd}, ld], Join[{pa}, la], Join[{pb}, lb]]] +
				If[pd > Length[RealScalarList], 0,  \[CapitalLambda]Y[Join[{pd}, ld], Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc]]]
			) //.subScalarInvariants//.{tr[adj[a_], b_]:>tr[b, adj[a]]};
			beta += - 3*24 Sum[Sqr[ListGauge[[ii,1]]]\[CapitalLambda]S[ii][Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]], {ii, 1, NumberOfSubgroups}]//.subScalarInvariants;
			beta += If[
				pa <= Length[RealScalarList] && pb <= Length[RealScalarList] && pc <= Length[RealScalarList] && pd <= Length[RealScalarList] && !SGaugeSinglet[pa] && !SGaugeSinglet[pb] && !SGaugeSinglet[pc] && !SGaugeSinglet[pd]
				,
				3 Sum[Sqr[ListGauge[[ii,1]]] Sqr[ListGauge[[ii2,1]]] (
					As[ii, ii2][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]] +
					As[ii, ii2][Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb], Prepend[ld, pd]] +
					As[ii, ii2][Prepend[la, pa], Prepend[lc, pc], Prepend[ld, pd], Prepend[lb, pb]] +
					As[ii, ii2][Prepend[lb, pb], Prepend[la, pa], Prepend[lc, pc], Prepend[ld, pd]] +
					As[ii, ii2][Prepend[lb, pb], Prepend[lc, pc], Prepend[la, pa], Prepend[ld, pd]] +
					As[ii, ii2][Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd], Prepend[la, pa]]
				), {ii, 1, NumberOfSubgroups}, {ii2, 1, NumberOfSubgroups}]//.subScalarInvariants,
				0
			];
			Return[beta/(24 Sqr[4\[Pi]])];
		];

		BetaQuartic[pa_, pb_, pc_, pd_, la_, lb_, lc_, ld_, 2] := Module[
			{beta, ss1, ss2, sIdx, ff, ii, ii2, ii3, x},
			beta = 0;
			beta += 1/2 * 24^3 (
				If[pa > Length[RealScalarList], 0, \[CapitalLambda]2S\[Lambda][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]] +
				If[pb > Length[RealScalarList], 0, \[CapitalLambda]2S\[Lambda][Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd], Prepend[la, pa]]] +
				If[pc > Length[RealScalarList], 0, \[CapitalLambda]2S\[Lambda][Prepend[lc, pc], Prepend[ld, pd], Prepend[la, pa], Prepend[lb, pb]]] +
				If[pd > Length[RealScalarList], 0, \[CapitalLambda]2S\[Lambda][Prepend[ld, pd], Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc]]]
			) //.subScalarInvariants;
			beta -= Power[24,3] (
				\[CapitalLambda]bar3[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]] +
				\[CapitalLambda]bar3[Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb], Prepend[ld, pd]] +
				\[CapitalLambda]bar3[Prepend[la, pa], Prepend[ld, pd], Prepend[lc, pc], Prepend[lb, pb]] +
				\[CapitalLambda]bar3[Prepend[lb, pb], Prepend[lc, pc], Prepend[la, pa], Prepend[ld, pd]] +
				\[CapitalLambda]bar3[Prepend[lb, pb], Prepend[ld, pd], Prepend[la, pa], Prepend[lc, pc]] +
				\[CapitalLambda]bar3[Prepend[lc, pc], Prepend[ld, pd], Prepend[la, pa], Prepend[lb, pb]]
			) //.subScalarInvariants;
			beta -= 2*Sqr[24] (
				\[CapitalLambda]bar2Y[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]] +
				\[CapitalLambda]bar2Y[Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb], Prepend[ld, pd]] +
				\[CapitalLambda]bar2Y[Prepend[la, pa], Prepend[ld, pd], Prepend[lb, pb], Prepend[lc, pc]]
			)//.subScalarInvariants;
			beta += 12*4 (
				Hbar\[Lambda][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]] +
				Hbar\[Lambda][Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb], Prepend[ld, pd]] +
				Hbar\[Lambda][Prepend[la, pa], Prepend[ld, pd], Prepend[lb, pb], Prepend[lc, pc]] +
				Hbar\[Lambda][Prepend[lc, pc], Prepend[ld, pd], Prepend[la, pa], Prepend[lb, pb]] +
				Hbar\[Lambda][Prepend[lb, pb], Prepend[ld, pd], Prepend[la, pa], Prepend[lc, pc]] +
				Hbar\[Lambda][Prepend[lb, pb], Prepend[lc, pc], Prepend[la, pa], Prepend[ld, pd]]
			)//.subScalarInvariants;
			beta -= 12 (
					If[pa > Length[RealScalarList], 0, 3 H2S\[Lambda][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]] + 2 Hbar2S\[Lambda][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]] +
					If[pb > Length[RealScalarList], 0, 3 H2S\[Lambda][Prepend[lb,pb], Prepend[lc,pc], Prepend[ld,pd], Prepend[la,pa]] + 2 Hbar2S\[Lambda][Prepend[lb,pb], Prepend[lc,pc], Prepend[ld,pd], Prepend[la,pa]]] +
					If[pc > Length[RealScalarList], 0, 3 H2S\[Lambda][Prepend[lc,pc], Prepend[ld,pd], Prepend[la,pa], Prepend[lb,pb]] + 2 Hbar2S\[Lambda][Prepend[lc,pc], Prepend[ld,pd], Prepend[la,pa], Prepend[lb,pb]]] +
					If[pd > Length[RealScalarList], 0, 3 H2S\[Lambda][Prepend[ld, pd], Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc]] + 2 Hbar2S\[Lambda][Prepend[ld, pd], Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc]]]
				)//.subScalarInvariants;
			beta += 2(Perm[HY[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]])//.subScalarInvariants;
			beta += 2(Perm[HbarY[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]])//.subScalarInvariants;
			beta += 2(
				H3[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]] +
				H3[Prepend[la, pa], Prepend[lb, pb], Prepend[ld, pd], Prepend[lc, pc]] +
				H3[Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb], Prepend[ld, pd]] +
				H3[Prepend[la, pa], Prepend[lc, pc], Prepend[ld, pd], Prepend[lb, pb]] +
				H3[Prepend[la, pa], Prepend[ld, pd], Prepend[lb, pb], Prepend[lc, pc]] +
				H3[Prepend[la, pa], Prepend[ld, pd], Prepend[lc, pc], Prepend[lb, pb]] +
				H3[Prepend[lb, pb], Prepend[la, pa], Prepend[lc, pc], Prepend[ld, pd]] +
				H3[Prepend[lb, pb], Prepend[la, pa], Prepend[ld, pd], Prepend[lc, pc]] +
				H3[Prepend[lb, pb], Prepend[lc, pc], Prepend[la, pa], Prepend[ld, pd]] +
				H3[Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd], Prepend[la, pa]] +
				H3[Prepend[lb, pb], Prepend[ld, pd], Prepend[la, pa], Prepend[lc, pc]] +
				H3[Prepend[lb, pb], Prepend[ld, pd], Prepend[lc, pc], Prepend[la, pa]] +
				H3[Prepend[lc, pc], Prepend[la, pa], Prepend[lb, pb], Prepend[ld, pd]] +
				H3[Prepend[lc, pc], Prepend[la, pa], Prepend[ld, pd], Prepend[lb, pb]] +
				H3[Prepend[lc, pc], Prepend[lb, pb], Prepend[la, pa], Prepend[ld, pd]] +
				H3[Prepend[lc, pc], Prepend[lb, pb], Prepend[ld, pd], Prepend[la, pa]] +
				H3[Prepend[lc, pc], Prepend[ld, pd], Prepend[la, pa], Prepend[lb, pb]] +
				H3[Prepend[lc, pc], Prepend[ld, pd], Prepend[lb, pb], Prepend[la, pa]] +
				H3[Prepend[ld, pd], Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc]] +
				H3[Prepend[ld, pd], Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb]] +
				H3[Prepend[ld, pd], Prepend[lb, pb], Prepend[la, pa], Prepend[lc, pc]] +
				H3[Prepend[ld, pd], Prepend[lb, pb], Prepend[lc, pc], Prepend[la, pa]] +
				H3[Prepend[ld, pd], Prepend[lc, pc], Prepend[la, pa], Prepend[lb, pb]] +
				H3[Prepend[ld, pd], Prepend[lc, pc], Prepend[lb, pb], Prepend[la, pa]]
			)//.subScalarInvariants;
			beta += Sqr[24]*2 (
				\[CapitalLambda]bar2S[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]] +
				\[CapitalLambda]bar2S[Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb], Prepend[ld, pd]] +
				\[CapitalLambda]bar2S[Prepend[la, pa], Prepend[ld, pd], Prepend[lb, pb], Prepend[lc, pc]]
			)//.subScalarInvariants;
			beta -= (2 Perm[HF[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]])//.subScalarInvariants;
			beta += (Sum[Sqr[ListGauge[[ii,1]]](
				If[pa > Length[RealScalarList], 0, C2[RealScalarList[[pa, 1]] , ListGauge[[ii,1]]]] +
				If[pb > Length[RealScalarList], 0, C2[RealScalarList[[pb, 1]] , ListGauge[[ii,1]]]] +
				If[pc > Length[RealScalarList], 0, C2[RealScalarList[[pc, 1]] , ListGauge[[ii,1]]]] +
				If[pd > Length[RealScalarList], 0, C2[RealScalarList[[pd, 1]] , ListGauge[[ii,1]]]]
			), {ii, 1, NumberOfSubgroups}] (
				H[Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]] +
				H[Join[{pa}, la], Join[{pb}, lb], Join[{pd}, ld], Join[{pc}, lc]] +
				H[Join[{pa}, la], Join[{pc}, lc], Join[{pb}, lb], Join[{pd}, ld]] +
				H[Join[{pa}, la], Join[{pc}, lc], Join[{pd}, ld], Join[{pb}, lb]] +
				H[Join[{pa}, la], Join[{pd}, ld], Join[{pb}, lb], Join[{pc}, lc]] +
				H[Join[{pa}, la], Join[{pd}, ld], Join[{pc}, lc], Join[{pb}, lb]] +
				H[Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld], Join[{pa}, la]] +
				H[Join[{pb}, lb], Join[{pd}, ld], Join[{pc}, lc], Join[{pa}, la]] +
				H[Join[{pc}, lc], Join[{pb}, lb], Join[{pd}, ld], Join[{pa}, la]] +
				H[Join[{pc}, lc], Join[{pd}, ld], Join[{pb}, lb], Join[{pa}, la]] +
				H[Join[{pd}, ld], Join[{pb}, lb], Join[{pc}, lc], Join[{pa}, la]] +
				H[Join[{pd}, ld], Join[{pc}, lc], Join[{pb}, lb], Join[{pa}, la]]
			))//.subScalarInvariants;
			beta += 5*24 (
				If[pa > Length[RealScalarList], 0, Y2FSL[Prepend[la,pa], Prepend[lb,pb], Prepend[lc,pc], Prepend[ld,pd]]] +
				If[pb > Length[RealScalarList], 0, Y2FSL[Prepend[lb,pb], Prepend[lc,pc], Prepend[ld,pd], Prepend[la,pa]]] +
				If[pc > Length[RealScalarList], 0, Y2FSL[Prepend[lc,pc], Prepend[ld,pd], Prepend[la,pa], Prepend[lb,pb]]] +
				If[pd > Length[RealScalarList], 0, Y2FSL[Prepend[ld,pd], Prepend[la,pa], Prepend[lb,pb], Prepend[lc,pc]]]
			)//.subScalarInvariants;
			beta -= Sum[
				Sqr[ListGauge[[ii,1]]](
					 24*18*8 (
						 \[CapitalLambda]2g[ii][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]] +
						 \[CapitalLambda]2g[ii][Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb], Prepend[ld, pd]] +
						 \[CapitalLambda]2g[ii][Prepend[la, pa], Prepend[ld, pd], Prepend[lb, pb], Prepend[lc, pc]]
					)
				)//.subScalarInvariants,
				{ii, 1, NumberOfSubgroups}
			];
			beta -= Sum[
				Power[ListGauge[[ii,1]],4] (
					(35/3 C2[ListGauge[[ii,1]]] - 5/3 Sum[S2[WeylFermionList[[ff,1]], ListGauge[[ii,1]]], {ff, 1, Length[WeylFermionList]}] - 11/12 Sum[S2[RealScalarList[[ss1[0],1]], ListGauge[[ii,1]]], {ss1[0], 1, Length[RealScalarList]}])*24*\[CapitalLambda]S[ii][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]
				)//.subScalarInvariants,
				{ii, 1, NumberOfSubgroups}
			];
			beta += Sum[
				Sqr[ListGauge[[ii,1]] ListGauge[[ii2,1]]] Refine[
					60(
							A\[Lambda][ii,ii2][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]] +
							A\[Lambda][ii,ii2][Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb], Prepend[ld, pd]] +
							A\[Lambda][ii,ii2][Prepend[la, pa], Prepend[ld, pd], Prepend[lc, pc], Prepend[lb, pb]] +
							A\[Lambda][ii,ii2][Prepend[lb, pb], Prepend[lc, pc], Prepend[la, pa], Prepend[ld, pd]] +
							A\[Lambda][ii,ii2][Prepend[lb, pb], Prepend[ld, pd], Prepend[la, pa], Prepend[lc, pc]] +
							A\[Lambda][ii,ii2][Prepend[lc, pc], Prepend[ld, pd], Prepend[la, pa], Prepend[lb, pb]]
					) + 12 (
							Abar\[Lambda][ii,ii2][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]] +
							Abar\[Lambda][ii,ii2][Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb], Prepend[ld, pd]] +
							Abar\[Lambda][ii,ii2][Prepend[la, pa], Prepend[ld, pd], Prepend[lc, pc], Prepend[lb, pb]] +
							Abar\[Lambda][ii,ii2][Prepend[lb, pb], Prepend[lc, pc], Prepend[la, pa], Prepend[ld, pd]] +
							Abar\[Lambda][ii,ii2][Prepend[lb, pb], Prepend[ld, pd], Prepend[la, pa], Prepend[lc, pc]] +
							Abar\[Lambda][ii,ii2][Prepend[lc, pc], Prepend[ld, pd], Prepend[la, pa], Prepend[lb, pb]]
					) + 36 BetaQuartic[pa, pb, pc, pd, la, lb, lc, ld, 0] (
						If[pa > Length[RealScalarList], 0, C2[RealScalarList[[pa,1]], ListGauge[[ii,1]]] C2[RealScalarList[[pa,1]], ListGauge[[ii2,1]]]] +
						If[pb > Length[RealScalarList], 0, C2[RealScalarList[[pb,1]], ListGauge[[ii,1]]] C2[RealScalarList[[pb,1]], ListGauge[[ii2,1]]]] +
						If[pc > Length[RealScalarList], 0, C2[RealScalarList[[pc,1]], ListGauge[[ii,1]]] C2[RealScalarList[[pc,1]], ListGauge[[ii2,1]]]] +
						If[pd > Length[RealScalarList], 0, C2[RealScalarList[[pd,1]], ListGauge[[ii,1]]] C2[RealScalarList[[pd,1]], ListGauge[[ii2,1]]]]
					) - 1/2 (
						BY[ii,ii2][Prepend[la,pa],Prepend[lb,pb],Prepend[lc,pc],Prepend[ld,pd]]+
						BY[ii,ii2][Prepend[la,pa],Prepend[lb,pb],Prepend[ld,pd],Prepend[lc,pc]]+
						BY[ii,ii2][Prepend[la,pa],Prepend[lc,pc],Prepend[lb,pb],Prepend[ld,pd]]+
						BY[ii,ii2][Prepend[la,pa],Prepend[lc,pc],Prepend[ld,pd],Prepend[lb,pb]]+
						BY[ii,ii2][Prepend[la,pa],Prepend[ld,pd],Prepend[lb,pb],Prepend[lc,pc]]+
						BY[ii,ii2][Prepend[la,pa],Prepend[ld,pd],Prepend[lc,pc],Prepend[lb,pb]]+
						BY[ii,ii2][Prepend[lb,pb],Prepend[la,pa],Prepend[lc,pc],Prepend[ld,pd]]+
						BY[ii,ii2][Prepend[lb,pb],Prepend[la,pa],Prepend[ld,pd],Prepend[lc,pc]]+
						BY[ii,ii2][Prepend[lb,pb],Prepend[lc,pc],Prepend[la,pa],Prepend[ld,pd]]+
						BY[ii,ii2][Prepend[lb,pb],Prepend[lc,pc],Prepend[ld,pd],Prepend[la,pa]]+
						BY[ii,ii2][Prepend[lb,pb],Prepend[ld,pd],Prepend[la,pa],Prepend[lc,pc]]+
						BY[ii,ii2][Prepend[lb,pb],Prepend[ld,pd],Prepend[lc,pc],Prepend[la,pa]]+
						BY[ii,ii2][Prepend[lc,pc],Prepend[la,pa],Prepend[lb,pb],Prepend[ld,pd]]+
						BY[ii,ii2][Prepend[lc,pc],Prepend[la,pa],Prepend[ld,pd],Prepend[lb,pb]]+
						BY[ii,ii2][Prepend[lc,pc],Prepend[lb,pb],Prepend[la,pa],Prepend[ld,pd]]+
						BY[ii,ii2][Prepend[lc,pc],Prepend[lb,pb],Prepend[ld,pd],Prepend[la,pa]]+
						BY[ii,ii2][Prepend[lc,pc],Prepend[ld,pd],Prepend[la,pa],Prepend[lb,pb]]+
						BY[ii,ii2][Prepend[lc,pc],Prepend[ld,pd],Prepend[lb,pb],Prepend[la,pa]]+
						BY[ii,ii2][Prepend[ld,pd],Prepend[la,pa],Prepend[lb,pb],Prepend[lc,pc]]+
						BY[ii,ii2][Prepend[ld,pd],Prepend[la,pa],Prepend[lc,pc],Prepend[lb,pb]]+
						BY[ii,ii2][Prepend[ld,pd],Prepend[lb,pb],Prepend[la,pa],Prepend[lc,pc]]+
						BY[ii,ii2][Prepend[ld,pd],Prepend[lb,pb],Prepend[lc,pc],Prepend[la,pa]]+
						BY[ii,ii2][Prepend[ld,pd],Prepend[lc,pc],Prepend[la,pa],Prepend[lb,pb]]+
						BY[ii,ii2][Prepend[ld,pd],Prepend[lc,pc],Prepend[lb,pb],Prepend[la,pa]]
					) + 5 (
						BbarY[ii,ii2][Prepend[la,pa],Prepend[lb,pb],Prepend[lc,pc],Prepend[ld,pd]]+
						BbarY[ii,ii2][Prepend[la,pa],Prepend[lb,pb],Prepend[ld,pd],Prepend[lc,pc]]+
						BbarY[ii,ii2][Prepend[la,pa],Prepend[lc,pc],Prepend[lb,pb],Prepend[ld,pd]]+
						BbarY[ii,ii2][Prepend[la,pa],Prepend[lc,pc],Prepend[ld,pd],Prepend[lb,pb]]+
						BbarY[ii,ii2][Prepend[la,pa],Prepend[ld,pd],Prepend[lb,pb],Prepend[lc,pc]]+
						BbarY[ii,ii2][Prepend[la,pa],Prepend[ld,pd],Prepend[lc,pc],Prepend[lb,pb]]+
						BbarY[ii,ii2][Prepend[lb,pb],Prepend[la,pa],Prepend[lc,pc],Prepend[ld,pd]]+
						BbarY[ii,ii2][Prepend[lb,pb],Prepend[la,pa],Prepend[ld,pd],Prepend[lc,pc]]+
						BbarY[ii,ii2][Prepend[lb,pb],Prepend[lc,pc],Prepend[la,pa],Prepend[ld,pd]]+
						BbarY[ii,ii2][Prepend[lb,pb],Prepend[lc,pc],Prepend[ld,pd],Prepend[la,pa]]+
						BbarY[ii,ii2][Prepend[lb,pb],Prepend[ld,pd],Prepend[la,pa],Prepend[lc,pc]]+
						BbarY[ii,ii2][Prepend[lb,pb],Prepend[ld,pd],Prepend[lc,pc],Prepend[la,pa]]+
						BbarY[ii,ii2][Prepend[lc,pc],Prepend[la,pa],Prepend[lb,pb],Prepend[ld,pd]]+
						BbarY[ii,ii2][Prepend[lc,pc],Prepend[la,pa],Prepend[ld,pd],Prepend[lb,pb]]+
						BbarY[ii,ii2][Prepend[lc,pc],Prepend[lb,pb],Prepend[la,pa],Prepend[ld,pd]]+
						BbarY[ii,ii2][Prepend[lc,pc],Prepend[lb,pb],Prepend[ld,pd],Prepend[la,pa]]+
						BbarY[ii,ii2][Prepend[lc,pc],Prepend[ld,pd],Prepend[la,pa],Prepend[lb,pb]]+
						BbarY[ii,ii2][Prepend[lc,pc],Prepend[ld,pd],Prepend[lb,pb],Prepend[la,pa]]+
						BbarY[ii,ii2][Prepend[ld,pd],Prepend[la,pa],Prepend[lb,pb],Prepend[lc,pc]]+
						BbarY[ii,ii2][Prepend[ld,pd],Prepend[la,pa],Prepend[lc,pc],Prepend[lb,pb]]+
						BbarY[ii,ii2][Prepend[ld,pd],Prepend[lb,pb],Prepend[la,pa],Prepend[lc,pc]]+
						BbarY[ii,ii2][Prepend[ld,pd],Prepend[lb,pb],Prepend[lc,pc],Prepend[la,pa]]+
						BbarY[ii,ii2][Prepend[ld,pd],Prepend[lc,pc],Prepend[la,pa],Prepend[lb,pb]]+
						BbarY[ii,ii2][Prepend[ld,pd],Prepend[lc,pc],Prepend[lb,pb],Prepend[la,pa]]
					)
				]//.subScalarInvariants,
				{ii, 1, NumberOfSubgroups},
				{ii2, 1, NumberOfSubgroups}
			];
			beta += If[
				pa <= Length[RealScalarList] && pb <= Length[RealScalarList] && pc <= Length[RealScalarList] && pd <= Length[RealScalarList] && !SGaugeSinglet[pa] && !SGaugeSinglet[pb] && !SGaugeSinglet[pc] && !SGaugeSinglet[pd],
				Sum[
					(
						As[ii, ii2][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]] +
						As[ii, ii2][Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb], Prepend[ld, pd]] +
						As[ii, ii2][Prepend[la, pa], Prepend[lc, pc], Prepend[ld, pd], Prepend[lb, pb]] +
						As[ii, ii2][Prepend[lb, pb], Prepend[la, pa], Prepend[lc, pc], Prepend[ld, pd]] +
						As[ii, ii2][Prepend[lb, pb], Prepend[lc, pc], Prepend[la, pa], Prepend[ld, pd]] +
						As[ii, ii2][Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd], Prepend[la, pa]]
					)(
						Sqr[ListGauge[[ii2,1]]] Power[ListGauge[[ii,1]],4] (
							161/6 C2[ListGauge[[ii,1]]] -
							16/3 Sum[S2[WeylFermionList[[ff,1]], ListGauge[[ii,1]]], {ff, 1, Length[WeylFermionList]}] -
							7/3 Sum[S2[RealScalarList[[ss1[0],1]], ListGauge[[ii,1]]], {ss1[0], 1, Length[RealScalarList]}]
						) - 15/2 Sum[Sqr[ListGauge[[ii,1]] ListGauge[[ii2,1]] ListGauge[[ii3,1]]](
							If[pa > Length[RealScalarList], 0, C2[RealScalarList[[pa,1]], ListGauge[[ii3,1]]]] +
							If[pb > Length[RealScalarList], 0, C2[RealScalarList[[pb,1]], ListGauge[[ii3,1]]]] +
							If[pc > Length[RealScalarList], 0, C2[RealScalarList[[pc,1]], ListGauge[[ii3,1]]]] +
							If[pd > Length[RealScalarList], 0, C2[RealScalarList[[pd,1]], ListGauge[[ii3,1]]]]
						), {ii3, 1, NumberOfSubgroups}]
					)//.subScalarInvariants,
					{ii, 1, NumberOfSubgroups},
					{ii2, 1, NumberOfSubgroups}
				],
				0
			];
			beta += 54 Sum[ Power[ListGauge[[ii,1]], 6] (
			Ag[ii][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]] +
			Ag[ii][Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb], Prepend[ld, pd]] +
			Ag[ii][Prepend[la, pa], Prepend[lc, pc], Prepend[ld, pd], Prepend[lb, pb]] +
			Ag[ii][Prepend[ld, pd], Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc]] +
			Ag[ii][Prepend[ld, pd], Prepend[la, pa], Prepend[lc, pc], Prepend[lb, pb]] +
			Ag[ii][Prepend[ld, pd], Prepend[lc, pc], Prepend[la, pa], Prepend[lb, pb]]
			), {ii, 1, NumberOfSubgroups}]//.subScalarInvariants;
			Return[beta/(24 Power[4 \[Pi], 4])];
		];

		BetaVEV[va_, 0] := va;

		BetaVEV[va_, 1] := Module[
			{beta, vb, ii},
			beta = 0;
			beta += Sum[
				Sqr[ListGauge[[ii,1]]] ( 3 + \[Xi]) C2[RealScalarList[[ListVEV[[vb,3,1]],1]],ListGauge[[ii,1]]] TensorDelta[ListVEV[[va,3]],ListVEV[[vb,3]]] ListVEV[[vb,2]] ListVEV[[vb,1]],
				{vb, 1, Dimensions[ListVEV][[1]]},
				{ii, 1, NumberOfSubgroups}
			];
			beta -= Sum[
				SimplifyProduct[(Y2S[ListVEV[[va,3]], ListVEV[[vb,3]]] ListVEV[[vb,2]] ListVEV[[vb,1]])/.subScalarInvariants],
				{vb, 1, Dimensions[ListVEV][[1]]}
			];
			Return[beta/( ListVEV[[va,2]] Power[4 \[Pi], 2])];
		];

		BetaVEV[va_, 2] := Module[
			{beta, vb, ii1, ii2, ff, ss},
			beta = 0;
			beta += Sum[
				Power[ListGauge[[ii1,1]], 4] C2[RealScalarList[[ListVEV[[va,3,1]],1]], ListGauge[[ii1,1]]] TensorDelta[ListVEV[[va,3]],ListVEV[[vb,3]]](
					(35/3 + 3/2 \[Xi] - 3/4 Sqr[\[Xi]]) C2[ListGauge[[ii1,1]]]
					- 5/3 Sum[S2[WeylFermionList[[ff,1]], ListGauge[[ii1,1]]], {ff, 1, Length[WeylFermionList]}]
					- 11/12 Sum[S2[RealScalarList[[ss,1]], ListGauge[[ii1,1]]], {ss, 1, Length[RealScalarList]}]
				) ListVEV[[vb,2]] ListVEV[[vb,1]],
				{vb, 1, Dimensions[ListVEV][[1]]},
				{ii1, 1, NumberOfSubgroups}
			];
			beta += Sum[
				Sqr[ListGauge[[ii1,1]] ListGauge[[ii2,1]]] C2[RealScalarList[[ListVEV[[va,3,1]],1]], ListGauge[[ii1,1]]] TensorDelta[ListVEV[[va,3]],ListVEV[[vb,3]]](
					(2\[Xi](1 + \[Xi]) - 3/2) C2[RealScalarList[[ListVEV[[vb,3,1]],1]], ListGauge[[ii2,1]]]
				) ListVEV[[vb,2]] ListVEV[[vb,1]],
				{vb, 1, Dimensions[ListVEV][[1]]},
				{ii1, 1, NumberOfSubgroups},
				{ii2, 1, NumberOfSubgroups}
			];
			beta += Sum[
				(-1/2 \[CapitalLambda]2S[ListVEV[[va,3]], ListVEV[[vb,3]]] + 3/2 H2S[ListVEV[[va,3]], ListVEV[[vb,3]]] + Hbar2S[ListVEV[[va,3]], ListVEV[[vb,3]]]) ListVEV[[vb,2]] ListVEV[[vb,1]] /. subScalarInvariants,
				{vb, 1, Dimensions[ListVEV][[1]]}
			];
			beta -= Sum[
				2\[Xi] Sum[ Sqr[ListGauge[[ii1,1]]] C2[RealScalarList[[ListVEV[[va,3,1]],1]], ListGauge[[ii1,1]]], {ii1, 1, NumberOfSubgroups}] Y2S[ListVEV[[va,3]], ListVEV[[vb,3]]] ListVEV[[vb,2]] ListVEV[[vb,1]] /. subScalarInvariants,
				{vb, 1, Dimensions[ListVEV][[1]]}
			];
			beta -= 5 Sum[Y2FS[ListVEV[[va,3]], ListVEV[[vb,3]]] ListVEV[[vb,2]] ListVEV[[vb,1]]/. subScalarInvariants, {vb, 1, Dimensions[ListVEV][[1]]}];
			Return[beta/( ListVEV[[va,2]] Power[4 \[Pi], 4])];
		];

		(* Backend for anomalous dimensions *)

		(* Fermion anomalous dimensions *)
		FGamma[f1_, f2_, l1_, l2_, 0] := TensorDelta[l1,l2] KroneckerDelta[AdjWeylFermionList[[f1,3]],f2]/2;

		FGamma[f1_, f2_, l1_, l2_, 1] := Module[
			{gamma, ii, ss, x},
			gamma = 0;
			gamma += 1/2 Sum[
				ContractSum@@Join[
					{
						SolveProd2[Yuk[ss[0]], adj[Yuk[ss[0]]], Prepend[l1, f1], Prepend[l2, f2], Prepend[Function[{x}, {ss[2+x], ss[2+x]}]/@Range[NumberOfSubgroups], {ss[1], ss[2], ss[1], ss[2]}]],
						{ss[1], 1, RealScalarList[[ss[0], 2, 1]]},
						{ss[2], 1, RealScalarList[[ss[0], 2, 2]]}
					},
					Function[{x}, {ss[2+x], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups]
				],
				{ss[0], 1, Length[RealScalarList]}
			]//SimplifyProduct;
			gamma += \[Xi]/2 Sum[
				Sqr[ListGauge[[ii,1]]] TensorDelta[l1,l2] KroneckerDelta[AdjWeylFermionList[[f1,3]],f2] C2[WeylFermionList[[AdjWeylFermionList[[f1,2]], 1]], ListGauge[[ii,1]]],
				{ii, 1, NumberOfSubgroups}
			];
			Return[gamma/Power[4 \[Pi], 2]];
		];

		FGamma[f1_, f2_, l1_, l2_, 2] := Module[
			{gamma, ii1, ii2, ff, ss1, ss2, x},
			gamma = 0;
			gamma -= 1/8 Sum[
				ContractSum@@Join[
					{
						SolveProd4[Yuk[ss1[0]], adj[Yuk[ss2[0]]], Yuk[ss2[0]], adj[Yuk[ss1[0]]], Prepend[l1, f1], Prepend[l2, f2], Prepend[Function[{x}, {ss1[2+x], ss2[2+x], ss2[2+x], ss1[2+x]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], ss2[1], ss2[2], ss2[1], ss2[2], ss1[1], ss1[2]}]],
						{ss1[1], 1, RealScalarList[[ss1[0], 2, 1]]},
						{ss1[2], 1, RealScalarList[[ss1[0], 2, 2]]},
						{ss2[1], 1, RealScalarList[[ss2[0], 2, 1]]},
						{ss2[2], 1, RealScalarList[[ss2[0], 2, 2]]}
					},
					Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
					Function[{x}, {ss2[2+x], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
				],
				{ss1[0], 1, Length[RealScalarList]},
				{ss2[0], 1, Length[RealScalarList]}
			]//SimplifyProduct;
			gamma -= 3/4 Sum[
				ContractSum@@Join[
					{
						SolveProd2[Yuk[ss1[0]], adj[Yuk[ss2[0]]], Prepend[l1, f1], Prepend[l2, f2], Prepend[Function[{x}, {ss1[2+x], ss2[2+x]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], ss2[1], ss2[2]}]] (Y2S[ss1/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2]]//.subScalarInvariants),
						{ss1[1], 1, RealScalarList[[ss1[0], 2, 1]]},
						{ss1[2], 1, RealScalarList[[ss1[0], 2, 2]]},
						{ss2[1], 1, RealScalarList[[ss2[0], 2, 1]]},
						{ss2[2], 1, RealScalarList[[ss2[0], 2, 2]]}
					},
					Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
					Function[{x}, {ss2[2+x], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
				],
				{ss1[0], 1, Length[RealScalarList]},
				{ss2[0], 1, Length[RealScalarList]}
			]//SimplifyProduct;
			gamma += Sum[
				ContractSum@@Join[
					{
						SolveProd2[Yuk[ss1[0]], adj[Yuk[ss1[0]]], Prepend[l1, f1], Prepend[l2, f2], Prepend[Function[{x}, {ss1[2+x], ss1[2+x]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], ss1[1], ss1[2]}]],
						{ss1[1], 1, RealScalarList[[ss1[0], 2, 1]]},
						{ss1[2], 1, RealScalarList[[ss1[0], 2, 2]]}
					},
					Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
				] Sqr[ListGauge[[ii1,1]]] (
					9/2 C2[RealScalarList[[ss1[0], 1]], ListGauge[[ii1, 1]]] -
					7/4 C2[WeylFermionList[[AdjWeylFermionList[[f1,2]], 1]], ListGauge[[ii1, 1]]]
				),
				{ss1[0], 1, Length[RealScalarList]},
				{ii1, 1, NumberOfSubgroups}
			]//SimplifyProduct;
			gamma -= 1/4 Sum[
				ContractSum@@Join[
					{
						SolveProd3[Yuk[ss1[0]], Delt[ff], adj[Yuk[ss1[0]]], Prepend[l1, f1], Prepend[l2, f2], Prepend[Function[{x}, {ss1[2+x], ss1[2+x], ss1[2+x]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], ss1[1], ss1[2], ss1[1], ss1[2]}]],
						{ss1[1], 1, RealScalarList[[ss1[0], 2, 1]]},
						{ss1[2], 1, RealScalarList[[ss1[0], 2, 2]]}
					},
					Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
				] Sqr[ListGauge[[ii1,1]]] C2[WeylFermionList[[ff,1]], ListGauge[[ii1,1]]],
				{ss1[0], 1, Length[RealScalarList]},
				{ff, 1, Length[WeylFermionList]},
				{ii1, 1, NumberOfSubgroups}
			]//SimplifyProduct;
			gamma += Sum[
				(
					(25/4 + 2 \[Xi] + 1/4 Sqr[\[Xi]]) C2[ListGauge[[ii1,1]]] -
					Sum[S2[WeylFermionList[[ff,1]], ListGauge[[ii1,1]]], {ff, 1, Length[WeylFermionList]}] -
					1/4 Sum[S2[RealScalarList[[ss1[0],1]], ListGauge[[ii1,1]]], {ss1[0], 1, Length[RealScalarList]}]
				) C2[WeylFermionList[[AdjWeylFermionList[[f1,2]], 1]], ListGauge[[ii1,1]]] Power[ListGauge[[ii1,1]],4] -
				3/2 Sum[
					Sqr[ListGauge[[ii1,1]] ListGauge[[ii2,1]]] C2[WeylFermionList[[AdjWeylFermionList[[f1,2]],1]], ListGauge[[ii1,1]]] C2[WeylFermionList[[AdjWeylFermionList[[f1,2]],1]], ListGauge[[ii2,1]]],
					{ii2, 1, NumberOfSubgroups}
				],
				{ii1, 1, NumberOfSubgroups}
			] TensorDelta[l1,l2] KroneckerDelta[AdjWeylFermionList[[f1,3]],f2]/2;
			Return[gamma/Power[4 \[Pi], 4]];
		];

		(* Scalar anomalous dimensions *)
		SGamma[pa_, pb_, la_, lb_, 0] := KroneckerDelta[pa, pb] TensorDelta[la, lb];

		SGamma[pa_, pb_, la_, lb_, 1] := Module[
			{gamma, ii},
			gamma = 0;
			gamma += (Y2S[Prepend[la,pa], Prepend[lb,pb]] //. subScalarInvariants)//SimplifyProduct;
			gamma -= KroneckerDelta[pa, pb] TensorDelta[la, lb] (3 - \[Xi]) Sum[ Sqr[ListGauge[[ii,1]]] C2[RealScalarList[[pa, 1]], ListGauge[[ii,1]]], {ii, 1, NumberOfSubgroups}];
			Return[gamma/Power[4 \[Pi], 2]];
		];

		SGamma[pa_, pb_, la_, lb_, 2] := Module[
			{gamma, ii1, ii2, ff, ss},
			gamma = 0;
			gamma -= KroneckerDelta[pa, pb] TensorDelta[la, lb] Sum[
				Power[ListGauge[[ii1, 1]], 4] C2[RealScalarList[[pa,1]], ListGauge[[ii1,1]]](
					(35/3 - 2 \[Xi] - Sqr[\[Xi]]/4) C2[ListGauge[[ii1,1]]] -
					5/3 Sum[S2[WeylFermionList[[ff,1]], ListGauge[[ii1,1]]], {ff, 1, Length[WeylFermionList]}] -
					11/12 Sum[S2[RealScalarList[[ss,1]], ListGauge[[ii1,1]]], {ss, 1, Length[RealScalarList]}]
				),
				{ii1, 1, NumberOfSubgroups}
			];
			gamma += 1/2 \[CapitalLambda]2S[Prepend[la,pa], Prepend[lb,pb]] //.subScalarInvariants;
			gamma += 3/2 Sum[Sqr[ListGauge[[ii1,1]] ListGauge[[ii2,1]]] C2[RealScalarList[[pa,1]], ListGauge[[ii1,1]]] C2[RealScalarList[[pa,1]], ListGauge[[ii2,1]]], {ii1, 1, NumberOfSubgroups}, {ii2, 1, NumberOfSubgroups}] KroneckerDelta[pa, pb] TensorDelta[la, lb];
			gamma -= 3/2 (H2S[Prepend[la,pa], Prepend[lb,pb]] //. subScalarInvariants)//SimplifyProduct;
			gamma -= (Hbar2S[Prepend[la,pa], Prepend[lb,pb]] //. subScalarInvariants)//SimplifyProduct;
			gamma += 5 (Y2FS[Prepend[la,pa], Prepend[lb,pb]] //. subScalarInvariants)//SimplifyProduct;
			Return[gamma/Power[4 \[Pi], 4]];
		];

		(* Checks if there are couplings missing  allowed by symmeties *)

		CheckYukawa[loop_, func_:(#&)] := Block[
			{treeL,loopL,f1,f2,s,res,assHold,i,pos},
			assHold = $Assumptions;
			$Assumptions = $Assumptions && And@@((Element[#,Integers]&&(#>=1))/@Join[{gen[S,1], gen[S,2], gen[F,1], gen[F,2]}, Flatten[{gauge[S,#], gauge[F,1,#], gauge[F,2,#]}& /@ Range[NumberOfSubgroups]]]);
			res = {};
			For[f1=1, f1<=Length[AdjWeylFermionList], f1++,
				For[f2=1, f2<=f1, f2++,
					For[s=1, s<=Length[RealScalarList], s++,
						treeL = ExtractIndexStructure[
							func[\[Beta][
								RealScalarList[[s,1]],
								AdjWeylFermionList[[f1,1]],
								AdjWeylFermionList[[f2,1]],
								Join[
									{
										If[RealScalarList[[s,2,1]] === 1, 1, gen[S,1]],
										If[RealScalarList[[s,2,2]] === 1, 1, gen[S,2]]
									},
									(If[SMultiplicity[s,#] === 1, 1, gauge[S,#]])&/@Range[NumberOfSubgroups]
								],
								Join[
									{ If[WeylFermionList[[AdjWeylFermionList[[f1,2]],2]] === 1, 1, gen[F,1]] },
									(If[FMultiplicity[AdjWeylFermionList[[f1,2]],#] === 1, 1, gauge[F,1,#]])&/@Range[NumberOfSubgroups]
								],
								Join[
									{ If[WeylFermionList[[AdjWeylFermionList[[f2,2]],2]] === 1, 1, gen[F,2]] },
									(If[FMultiplicity[AdjWeylFermionList[[f2,2]],#] === 1, 1, gauge[F,2,#]])&/@Range[NumberOfSubgroups]
								],
								0
							]],
							Join[{gen[S,1], gen[S,2], gen[F,1], gen[F,2]}, Flatten[{gauge[S,#], gauge[F,1,#], gauge[F,2,#]}& /@ Range[NumberOfSubgroups]]]
						]/.{Factorize->List};
						loopL = ExtractIndexStructure[
							func[\[Beta][
								RealScalarList[[s,1]],
								AdjWeylFermionList[[f1,1]],
								AdjWeylFermionList[[f2,1]],
								Join[
									{
										If[RealScalarList[[s,2,1]] === 1, 1, gen[S,1]],
										If[RealScalarList[[s,2,2]] === 1, 1, gen[S,2]]
									},
									(If[SMultiplicity[s,#] === 1, 1, gauge[S,#]])&/@Range[NumberOfSubgroups]
								],
								Join[
									{ If[WeylFermionList[[AdjWeylFermionList[[f1,2]],2]] === 1, 1, gen[F,1]] },
									(If[FMultiplicity[AdjWeylFermionList[[f1,2]],#] === 1, 1, gauge[F,1,#]])&/@Range[NumberOfSubgroups]
								],
								Join[
									{ If[WeylFermionList[[AdjWeylFermionList[[f2,2]],2]] === 1, 1, gen[F,2]] },
									(If[FMultiplicity[AdjWeylFermionList[[f2,2]],#] === 1, 1, gauge[F,2,#]])&/@Range[NumberOfSubgroups]
								],
								loop
							]],
							Join[{gen[S,1], gen[S,2], gen[F,1], gen[F,2]}, Flatten[{gauge[S,#], gauge[F,1,#], gauge[F,2,#]}& /@ Range[NumberOfSubgroups]]]
						]/.{Factorize->List};
						For[i=1, i<=Length[treeL], i++,
							pos=Flatten[Position[res, {RealScalarList[[s,1]], AdjWeylFermionList[[f1,1]], AdjWeylFermionList[[f2,1]], treeL[[i,2]], _, _}]];
							If[pos==={},
								res = Append[res, {RealScalarList[[s,1]], AdjWeylFermionList[[f1,1]], AdjWeylFermionList[[f2,1]], treeL[[i,2]], treeL[[i,1]], 0}];,
								res[[pos[[1]], 5]] += treeL[[i,1]];
							];
						];
						For[i=1, i<=Length[loopL], i++,
							pos=Flatten[Position[res, {RealScalarList[[s,1]], AdjWeylFermionList[[f1,1]], AdjWeylFermionList[[f2,1]], loopL[[i,2]], _, _}]];
							If[pos==={},
								res = Append[res, {RealScalarList[[s,1]], AdjWeylFermionList[[f1,1]], AdjWeylFermionList[[f2,1]], loopL[[i,2]], 0, loopL[[i,1]]}];,
								res[[pos[[1]], 6]] += loopL[[i,1]];
							];
						];
					];
				];
			];
			$Assumptions = assHold;
			Return[res//.{FF1___, {_, _, _, _, 0, 0}, FF2___ } :> {FF1,FF2}];
		];

		CheckFermionMass[loop_, func_:(#&)] := Block[
			{treeL,loopL,f1,f2,res,assHold,i,pos},
			assHold = $Assumptions;
			$Assumptions = $Assumptions && And@@((Element[#,Integers]&&(#>=1))/@Join[{gen[F,1], gen[F,2]}, Flatten[{gauge[F,1,#], gauge[F,2,#]}& /@ Range[NumberOfSubgroups]]]);
			res = {};
			For[f1=1, f1<=Length[AdjWeylFermionList], f1++,
				For[f2=1, f2<=f1, f2++,
					treeL = ExtractIndexStructure[
						func[\[Beta][
							AdjWeylFermionList[[f1,1]],
							AdjWeylFermionList[[f2,1]],
							Join[
								{ If[WeylFermionList[[AdjWeylFermionList[[f1,2]],2]] === 1, 1, gen[F,1]] },
								(If[FMultiplicity[AdjWeylFermionList[[f1,2]],#] === 1, 1, gauge[F,1,#]])&/@Range[NumberOfSubgroups]
							],
							Join[
								{ If[WeylFermionList[[AdjWeylFermionList[[f2,2]],2]] === 1, 1, gen[F,2]] },
								(If[FMultiplicity[AdjWeylFermionList[[f2,2]],#] === 1, 1, gauge[F,2,#]])&/@Range[NumberOfSubgroups]
							],
							0
						]],
						Join[{gen[F,1], gen[F,2]}, Flatten[{gauge[F,1,#], gauge[F,2,#]}& /@ Range[NumberOfSubgroups]]]
					]/.{Factorize->List};
					loopL = ExtractIndexStructure[
						func[\[Beta][
							AdjWeylFermionList[[f1,1]],
							AdjWeylFermionList[[f2,1]],
							Join[
								{ If[WeylFermionList[[AdjWeylFermionList[[f1,2]],2]] === 1, 1, gen[F,1]] },
								(If[FMultiplicity[AdjWeylFermionList[[f1,2]],#] === 1, 1, gauge[F,1,#]])&/@Range[NumberOfSubgroups]
							],
							Join[
								{ If[WeylFermionList[[AdjWeylFermionList[[f2,2]],2]] === 1, 1, gen[F,2]] },
								(If[FMultiplicity[AdjWeylFermionList[[f2,2]],#] === 1, 1, gauge[F,2,#]])&/@Range[NumberOfSubgroups]
							],
							loop
						]],
						Join[{gen[F,1], gen[F,2]}, Flatten[{gauge[F,1,#], gauge[F,2,#]}& /@ Range[NumberOfSubgroups]]]
					]/.{Factorize->List};
					For[i=1, i<=Length[treeL], i++,
						pos=Flatten[Position[res, {AdjWeylFermionList[[f1,1]], AdjWeylFermionList[[f2,1]], treeL[[i,2]], _, _}]];
						If[pos==={},
							res = Append[res, {AdjWeylFermionList[[f1,1]], AdjWeylFermionList[[f2,1]], treeL[[i,2]], treeL[[i,1]], 0}];,
							res[[pos[[1]], 4]] += treeL[[i,1]];
						];
					];
					For[i=1, i<=Length[loopL], i++,
						pos=Flatten[Position[res, {AdjWeylFermionList[[f1,1]], AdjWeylFermionList[[f2,1]], loopL[[i,2]], _, _}]];
						If[pos==={},
							res = Append[res, {AdjWeylFermionList[[f1,1]], AdjWeylFermionList[[f2,1]], loopL[[i,2]], 0, loopL[[i,1]]}];,
							res[[pos[[1]], 5]] += loopL[[i,1]];
						];
					];
				];
			];
			$Assumptions = assHold;
			Return[res//.{FF1___, { ___, 0, 0}, FF2___ } :> {FF1,FF2}];
		];

		CheckQuartic[loop_, func_:(#&)] := Block[
			{treeL, loopL, s1, s2, s3, s4, assHold, i, pos},
			assHold = $Assumptions;
			$Assumptions = $Assumptions && And@@((Element[#,Integers]&&(#>=1))/@Join[
				{gen[S,1,1], gen[S,1,2], gen[S,2,1], gen[S,2,2], gen[S,3,1], gen[S,3,2], gen[S,4,1], gen[S,4,2]},
				Flatten[{gauge[S,1,#], gauge[S,2,#], gauge[S,3,#], gauge[S,4,#]}& /@ Range[NumberOfSubgroups]]
			]);
			res = {};
			For[s1=1, s1<=Length[RealScalarList], s1++,
				For[s2=1, s2<=s1, s2++,
					For[s3=1, s3<=s2, s3++,
						For[s4=1, s4<=s3, s4++,
							treeL = ExtractIndexStructure[
								func[\[Beta][
									RealScalarList[[s1,1]],
									RealScalarList[[s2,1]],
									RealScalarList[[s3,1]],
									RealScalarList[[s4,1]],
									Join[
										{
											If[RealScalarList[[s1,2,1]] === 1, 1, gen[S,1,1]],
											If[RealScalarList[[s1,2,2]] === 1, 1, gen[S,1,2]]
										},
										(If[SMultiplicity[s1,#] === 1, 1, gauge[S,1,#]])&/@Range[NumberOfSubgroups]
									],
									Join[
										{
											If[RealScalarList[[s2,2,1]] === 1, 1, gen[S,2,1]],
											If[RealScalarList[[s2,2,2]] === 1, 1, gen[S,2,2]]
										},
										(If[SMultiplicity[s2,#] === 1, 1, gauge[S,2,#]])&/@Range[NumberOfSubgroups]
									],
									Join[
										{
											If[RealScalarList[[s3,2,1]] === 1, 1, gen[S,3,1]],
											If[RealScalarList[[s3,2,2]] === 1, 1, gen[S,3,2]]
										},
										(If[SMultiplicity[s3,#] === 1, 1, gauge[S,3,#]])&/@Range[NumberOfSubgroups]
									],
									Join[
										{
											If[RealScalarList[[s4,2,1]] === 1, 1, gen[S,4,1]],
											If[RealScalarList[[s4,2,2]] === 1, 1, gen[S,4,2]]
										},
										(If[SMultiplicity[s4,#] === 1, 1, gauge[S,4,#]])&/@Range[NumberOfSubgroups]
									],
									0
								]],
								Flatten[Join[
									{gen[S,1,1], gen[S,1,2], gen[S,2,1], gen[S,2,2], gen[S,3,1], gen[S,3,2], gen[S,4,1], gen[S,4,2]},
									{gauge[S,1,#], gauge[S,2,#], gauge[S,3,#], gauge[S,4,#]} /@ Range[NumberOfSubgroups]
								]]
							]/.{Factorize->List};
							loopL = ExtractIndexStructure[
								func[\[Beta][
									RealScalarList[[s1,1]],
									RealScalarList[[s2,1]],
									RealScalarList[[s3,1]],
									RealScalarList[[s4,1]],
									Join[
										{
											If[RealScalarList[[s1,2,1]] === 1, 1, gen[S,1,1]],
											If[RealScalarList[[s1,2,2]] === 1, 1, gen[S,1,2]]
										},
										(If[SMultiplicity[s1,#] === 1, 1, gauge[S,1,#]])&/@Range[NumberOfSubgroups]
									],
									Join[
										{
											If[RealScalarList[[s2,2,1]] === 1, 1, gen[S,2,1]],
											If[RealScalarList[[s2,2,2]] === 1, 1, gen[S,2,2]]
										},
										(If[SMultiplicity[s2,#] === 1, 1, gauge[S,2,#]])&/@Range[NumberOfSubgroups]
									],
									Join[
										{
											If[RealScalarList[[s3,2,1]] === 1, 1, gen[S,3,1]],
											If[RealScalarList[[s3,2,2]] === 1, 1, gen[S,3,2]]
										},
										(If[SMultiplicity[s3,#] === 1, 1, gauge[S,3,#]])&/@Range[NumberOfSubgroups]
									],
									Join[
										{
											If[RealScalarList[[s4,2,1]] === 1, 1, gen[S,4,1]],
											If[RealScalarList[[s4,2,2]] === 1, 1, gen[S,4,2]]
										},
										(If[SMultiplicity[s4,#] === 1, 1, gauge[S,4,#]])&/@Range[NumberOfSubgroups]
									],
									loop
								]],
								Flatten[Join[
									{gen[S,1,1], gen[S,1,2], gen[S,2,1], gen[S,2,2], gen[S,3,1], gen[S,3,2], gen[S,4,1], gen[S,4,2]},
									{gauge[S,1,#], gauge[S,2,#], gauge[S,3,#], gauge[S,4,#]} /@ Range[NumberOfSubgroups]
								]]
							]/.{Factorize->List};
							For[i=1, i<=Length[treeL], i++,
								pos=Flatten[Position[res, {RealScalarList[[s1,1]], RealScalarList[[s2,1]], RealScalarList[[s3,1]], RealScalarList[[s4,1]], treeL[[i,2]], _, _}]];
								If[pos==={},
									res = Append[res, {RealScalarList[[s1,1]], RealScalarList[[s2,1]], RealScalarList[[s3,1]], RealScalarList[[s4,1]], treeL[[i,2]], treeL[[i,1]], 0}];,
									res[[pos[[1]], 6]] += treeL[[i,1]];
								];
							];
							For[i=1, i<=Length[loopL], i++,
								pos=Flatten[Position[res, {RealScalarList[[s1,1]], RealScalarList[[s2,1]], RealScalarList[[s3,1]], RealScalarList[[s4,1]], loopL[[i,2]], _, _}]];
								If[pos==={},
									res = Append[res, {RealScalarList[[s1,1]], RealScalarList[[s2,1]], RealScalarList[[s3,1]], RealScalarList[[s4,1]], loopL[[i,2]], 0, loopL[[i,1]]}];,
									res[[pos[[1]], 7]] += loopL[[i,1]];
								];
							];
						];
					];
				];
			];
			$Assumptions = assHold;
			Return[res//.{FF1___, { ___, 0, 0}, FF2___ } :> {FF1,FF2}];
		];

		CheckCubic[loop_, func_:(#&)] := Block[
			{treeL, loopL, s1, s2, s3, assHold, i, pos},
			assHold = $Assumptions;
			$Assumptions = $Assumptions && And@@((Element[#,Integers]&&(#>=1))/@Join[
				{gen[S,1,1], gen[S,1,2], gen[S,2,1], gen[S,2,2], gen[S,3,1], gen[S,3,2]},
				Flatten[{gauge[S,1,#], gauge[S,2,#], gauge[S,3,#]}& /@ Range[NumberOfSubgroups]]
			]);
			res = {};
			For[s1=1, s1<=Length[RealScalarList], s1++,
				For[s2=1, s2<=s1, s2++,
					For[s3=1, s3<=s2, s3++,
						treeL = ExtractIndexStructure[
							func[\[Beta][
								RealScalarList[[s1,1]],
								RealScalarList[[s2,1]],
								RealScalarList[[s3,1]],
								Join[
									{
										If[RealScalarList[[s1,2,1]] === 1, 1, gen[S,1,1]],
										If[RealScalarList[[s1,2,2]] === 1, 1, gen[S,1,2]]
									},
									(If[SMultiplicity[s1,#] === 1, 1, gauge[S,1,#]])&/@Range[NumberOfSubgroups]
								],
								Join[
									{
										If[RealScalarList[[s2,2,1]] === 1, 1, gen[S,2,1]],
										If[RealScalarList[[s2,2,2]] === 1, 1, gen[S,2,2]]
									},
									(If[SMultiplicity[s2,#] === 1, 1, gauge[S,2,#]])&/@Range[NumberOfSubgroups]
								],
								Join[
									{
										If[RealScalarList[[s3,2,1]] === 1, 1, gen[S,3,1]],
										If[RealScalarList[[s3,2,2]] === 1, 1, gen[S,3,2]]
									},
									(If[SMultiplicity[s3,#] === 1, 1, gauge[S,3,#]])&/@Range[NumberOfSubgroups]
								],
								0
							]],
							Flatten[Join[
								{gen[S,1,1], gen[S,1,2], gen[S,2,1], gen[S,2,2], gen[S,3,1], gen[S,3,2]},
								{gauge[S,1,#], gauge[S,2,#], gauge[S,3,#]} /@ Range[NumberOfSubgroups]
							]]
						]/.{Factorize->List};
						loopL = ExtractIndexStructure[
							func[\[Beta][
								RealScalarList[[s1,1]],
								RealScalarList[[s2,1]],
								RealScalarList[[s3,1]],
								Join[
									{
										If[RealScalarList[[s1,2,1]] === 1, 1, gen[S,1,1]],
										If[RealScalarList[[s1,2,2]] === 1, 1, gen[S,1,2]]
									},
									(If[SMultiplicity[s1,#] === 1, 1, gauge[S,1,#]])&/@Range[NumberOfSubgroups]
								],
								Join[
									{
										If[RealScalarList[[s2,2,1]] === 1, 1, gen[S,2,1]],
										If[RealScalarList[[s2,2,2]] === 1, 1, gen[S,2,2]]
									},
									(If[SMultiplicity[s2,#] === 1, 1, gauge[S,2,#]])&/@Range[NumberOfSubgroups]
								],
								Join[
									{
										If[RealScalarList[[s3,2,1]] === 1, 1, gen[S,3,1]],
										If[RealScalarList[[s3,2,2]] === 1, 1, gen[S,3,2]]
									},
									(If[SMultiplicity[s3,#] === 1, 1, gauge[S,3,#]])&/@Range[NumberOfSubgroups]
								],
								loop
							]],
							Flatten[Join[
								{gen[S,1,1], gen[S,1,2], gen[S,2,1], gen[S,2,2], gen[S,3,1], gen[S,3,2]},
								{gauge[S,1,#], gauge[S,2,#], gauge[S,3,#]} /@ Range[NumberOfSubgroups]
							]]
						]/.{Factorize->List};
						For[i=1, i<=Length[treeL], i++,
							pos=Flatten[Position[res, {RealScalarList[[s1,1]], RealScalarList[[s2,1]], RealScalarList[[s3,1]], treeL[[i,2]], _, _}]];
							If[pos==={},
								res = Append[res, {RealScalarList[[s1,1]], RealScalarList[[s2,1]], RealScalarList[[s3,1]], treeL[[i,2]], treeL[[i,1]], 0}];,
								res[[pos[[1]], 5]] += treeL[[i,1]];
							];
						];
						For[i=1, i<=Length[loopL], i++,
							pos=Flatten[Position[res, {RealScalarList[[s1,1]], RealScalarList[[s2,1]], RealScalarList[[s3,1]], loopL[[i,2]], _, _}]];
							If[pos==={},
								res = Append[res, {RealScalarList[[s1,1]], RealScalarList[[s2,1]], RealScalarList[[s3,1]], loopL[[i,2]], 0, loopL[[i,1]]}];,
								res[[pos[[1]], 6]] += loopL[[i,1]];
							];
						];
					];
				];
			];
			$Assumptions = assHold;
			Return[res//.{FF1___, { ___, 0, 0}, FF2___ } :> {FF1,FF2}];
		];

	CheckScalarMass[loop_, func_:(#&)] := Block[
			{treeL, loopL, s1, s2, assHold, i, pos},
			assHold = $Assumptions;
			$Assumptions = $Assumptions && And@@((Element[#,Integers]&&(#>=1))/@Join[
				{gen[S,1,1], gen[S,1,2], gen[S,2,1], gen[S,2,2]},
				Flatten[{gauge[S,1,#], gauge[S,2,#]}& /@ Range[NumberOfSubgroups]]
			]);
			res = {};
			For[s1=1, s1<=Length[RealScalarList], s1++,
				For[s2=1, s2<=s1, s2++,
					treeL = ExtractIndexStructure[
						func[\[Beta][
							RealScalarList[[s1,1]],
							RealScalarList[[s2,1]],
							Join[
								{
									If[RealScalarList[[s1,2,1]] === 1, 1, gen[S,1,1]],
									If[RealScalarList[[s1,2,2]] === 1, 1, gen[S,1,2]]
								},
								(If[SMultiplicity[s1,#] === 1, 1, gauge[S,1,#]])&/@Range[NumberOfSubgroups]
							],
							Join[
								{
									If[RealScalarList[[s2,2,1]] === 1, 1, gen[S,2,1]],
									If[RealScalarList[[s2,2,2]] === 1, 1, gen[S,2,2]]
								},
								(If[SMultiplicity[s2,#] === 1, 1, gauge[S,2,#]])&/@Range[NumberOfSubgroups]
							],
							0
						]],
						Flatten[Join[
							{gen[S,1,1], gen[S,1,2], gen[S,2,1], gen[S,2,2]},
							{gauge[S,1,#], gauge[S,2,#]} /@ Range[NumberOfSubgroups]
						]]
					]/.{Factorize->List};
					loopL = ExtractIndexStructure[
						func[\[Beta][
							RealScalarList[[s1,1]],
							RealScalarList[[s2,1]],
							Join[
								{
									If[RealScalarList[[s1,2,1]] === 1, 1, gen[S,1,1]],
									If[RealScalarList[[s1,2,2]] === 1, 1, gen[S,1,2]]
								},
								(If[SMultiplicity[s1,#] === 1, 1, gauge[S,1,#]])&/@Range[NumberOfSubgroups]
							],
							Join[
								{
									If[RealScalarList[[s2,2,1]] === 1, 1, gen[S,2,1]],
									If[RealScalarList[[s2,2,2]] === 1, 1, gen[S,2,2]]
								},
								(If[SMultiplicity[s2,#] === 1, 1, gauge[S,2,#]])&/@Range[NumberOfSubgroups]
							],
							loop
						]],
						Flatten[Join[
							{gen[S,1,1], gen[S,1,2], gen[S,2,1], gen[S,2,2]},
							{gauge[S,1,#], gauge[S,2,#]} /@ Range[NumberOfSubgroups]
						]]
					]/.{Factorize->List};
					For[i=1, i<=Length[treeL], i++,
						pos=Flatten[Position[res, {RealScalarList[[s1,1]], RealScalarList[[s2,1]], treeL[[i,2]], _, _}]];
						If[pos==={},
							res = Append[res, {RealScalarList[[s1,1]], RealScalarList[[s2,1]], treeL[[i,2]], treeL[[i,1]], 0}];,
							res[[pos[[1]], 4]] += treeL[[i,1]];
						];
					];
					For[i=1, i<=Length[loopL], i++,
						pos=Flatten[Position[res, {RealScalarList[[s1,1]], RealScalarList[[s2,1]], loopL[[i,2]], _, _}]];
						If[pos==={},
							res = Append[res, {RealScalarList[[s1,1]], RealScalarList[[s2,1]], loopL[[i,2]], 0, loopL[[i,1]]}];,
							res[[pos[[1]], 5]] += loopL[[i,1]];
						];
					];
				];
			];
			$Assumptions = assHold;
			Return[res//.{FF1___, { ___, 0, 0}, FF2___ } :> {FF1,FF2}];
		];


		(* Definition of Invariants *)
		ComputeInvariants[] := Module[
			{i, f, s, sIdx, Y4Hold, assHold},
			subInvariants = {};
			If[NumberOfSubgroups==0 || Length[ListGauge], Return[];];
			For[i=1, i<=NumberOfSubgroups, i++,
				(* Gauge Boson Invariants *)
				If[ListGauge[[i,2]] === U && ListGauge[[i,3]] === 1 && ListGauge[[i,4,i]] === 0,
					(* Singulet U(1) *)
					subInvariants = Append[subInvariants, d[ListGauge[[i,1]]]->1];
					subInvariants = Append[subInvariants, C2[ListGauge[[i,1]]]->0];,
					(* not U(1) *)
					If[ListGauge[[i,4,i]] === 1,
						(* gauge singulet: *)
						subInvariants = Append[subInvariants, C2[ListGauge[[i]]]->0];,
						(* no singulet: *)
						(* Adjoint Rep in SU(N)*)
						If[ListGauge[[i,2]] === SU && ListGauge[[i,4,i]]===Sqr[ListGauge[[i,3]]]-1,
							subInvariants = Append[subInvariants, d[ListGauge[[i,1]]]->ListGauge[[i,4,i]]];
							subInvariants = Append[subInvariants, C2[ListGauge[[i,1]]]->ListGauge[[i,3]]];
						];
						(* Adjoint Rep in SO(N)*)
						If[ListGauge[[i,2]] === SO && ListGauge[[i,4,i]]===1/2 ListGauge[[i,3]](ListGauge[[i,3]]-1),
							subInvariants = Append[subInvariants, d[ListGauge[[i,1]]]->ListGauge[[i,4,i]]];
							subInvariants = Append[subInvariants, C2[ListGauge[[i,1]]]->1/2(ListGauge[[i,3]] - 2)];
						];
						(* Adjoint Rep in Sp(2N)*)
						If[ListGauge[[i,2]] === Sp && ListGauge[[i,4,i]]===1/2 ListGauge[[i,3]](ListGauge[[i,3]]+1),
							subInvariants = Append[subInvariants, d[ListGauge[[i,1]]]->ListGauge[[i,4,i]]];
							subInvariants = Append[subInvariants, C2[ListGauge[[i,1]]]->(1/2 ListGauge[[i,3]] + 1)];
						];
					];
				];
				(* Fermion Invariants *)
				If[WeylFermionList != {},
					For[f=1, f<=Length[WeylFermionList], f++,
						subInvariants = Append[subInvariants, d[WeylFermionList[[f,1]], ListGauge[[i,1]]]->FMultiplicity[f,i]];
						subInvariants = Append[subInvariants, T2[WeylFermionList[[f,1]], ListGauge[[i,1]]]->FMultiplicity[f,i]/FMultiplicity[f] S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]];
						(* SU(N) subgroup *)
						If[ListGauge[[i,2]] === SU,
							If[WeylFermionList[[f,3,i]] === 1,
								subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 0];
								Continue[];,
								(* Fundamental Representation *)
								If[WeylFermionList[[f,3,i]] === ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 (Sqr[WeylFermionList[[f,3,i]]]-1)/WeylFermionList[[f,3,i]]];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 FMultiplicity[f]/WeylFermionList[[f,3,i]]];
								];
								(* Adjoint Representation *)
								If[WeylFermionList[[f,3,i]] === Sqr[ListGauge[[i,3]]] - 1,
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> FMultiplicity[f]/WeylFermionList[[f,3,i]] ListGauge[[i,3]]];
								];
								(* Symmetric Representation *)
								If[WeylFermionList[[f,3,i]] === 1/2 ListGauge[[i,3]] (ListGauge[[i,3]] + 1),
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> (ListGauge[[i,3]] + 2)(ListGauge[[i,3]] - 1)/ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> FMultiplicity[f]/WeylFermionList[[f,3,i]] (1/2 ListGauge[[i,3]] + 1)];
								];
								(* Anitsymmetric Representation *)
								If[WeylFermionList[[f,3,i]] === 1/2 ListGauge[[i,3]] (ListGauge[[i,3]] - 1),
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> (ListGauge[[i,3]] - 2)(ListGauge[[i,3]] + 1)/ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> FMultiplicity[f]/WeylFermionList[[f,3,i]] (1/2 ListGauge[[i,3]] - 1)];
								];
							];
						];
						(* SO(N) subgroup *)
						If[ListGauge[[i,2]] === SO,
							If[WeylFermionList[[f,3,i]] === 1,
								subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 0];
								Continue[];,
								(* Fundamental Representation *)
								If[WeylFermionList[[f,3,i]] === ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/4 (ListGauge[[i,3]] - 1)];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 FMultiplicity[f]/WeylFermionList[[f,3,i]]];
								];
								(* Adjoint Representation *)
								If[WeylFermionList[[f,3,i]] === 1/2 ListGauge[[i,3]](ListGauge[[i,3]] - 1),
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 ( ListGauge[[i,3]] - 2)];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 (ListGauge[[i,3]] - 2) FMultiplicity[f]/WeylFermionList[[f,3,i]]];
								];
								(* Symmetric Representation *)
								If[WeylFermionList[[f,3,i]] === 1/2 ListGauge[[i,3]](ListGauge[[i,3]] + 1) - 1,
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 ( ListGauge[[i,3]])];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 (ListGauge[[i,3]] + 2) FMultiplicity[f]/WeylFermionList[[f,3,i]]];

								];
							];
						];
						(* SP(2N) subgroup *)
						If[ListGauge[[i,2]] === Sp,
							If[WeylFermionList[[f,3,i]] === 1,
								subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 0];
								Continue[];,
								(* Fundamental Representation *)
								If[WeylFermionList[[f,3,i]] === ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/4 (ListGauge[[i,3]] + 1)];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 FMultiplicity[f]/WeylFermionList[[f,3,i]]];
								];
								(* Antisymmetric Representation *)
								If[WeylFermionList[[f,3,i]] === 1/2 (ListGauge[[i,3]] - 2)(ListGauge[[i,3]] + 1) ,
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 ListGauge[[i,3]] ];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> (1/2 ListGauge[[i,3]] - 1) FMultiplicity[f]/WeylFermionList[[f,3,i]]];
								];
								(* Adjoint Representation *)
								If[WeylFermionList[[f,3,i]] === 1/2 ListGauge[[i,3]](ListGauge[[i,3]] + 1),
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> (1/2 ListGauge[[i,3]] + 1)];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> (1/2 ListGauge[[i,3]] + 1) FMultiplicity[f]/WeylFermionList[[f,3,i]]];
								];
							];
						];
						(* U(1) subgroup *)
						If[ListGauge[[i,2]] === U && ListGauge[[i,3]] === 1,
							subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]->Sqr[WeylFermionList[[f,3,i]]]];
							subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]->Sqr[WeylFermionList[[f,3,i]]] FMultiplicity[f]];
						];
					];
				];
				(* Scalar Invariants *)
				If[RealScalarList != {},
					For[s=1, s<=Length[RealScalarList], s++,
						subInvariants = Append[subInvariants, d[RealScalarList[[s,1]], ListGauge[[i,1]]]->SMultiplicity[s,i]];
						subInvariants = Append[subInvariants, T2[RealScalarList[[s,1]], ListGauge[[i,1]]]->SMultiplicity[s,i]/SMultiplicity[s] S2[RealScalarList[[s,1]], ListGauge[[i,1]]]];
						(* SU(N) subgroup *)
						If[ListGauge[[i,2]] === SU,
							If[RealScalarList[[s,3,i]] === 1,
								subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 0];
								Continue[];,
								(* Fundamental Representation *)
								If[RealScalarList[[s,3,i]] === ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/2 (Sqr[RealScalarList[[s,3,i]]]-1)/RealScalarList[[s,3,i]]];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/2 SMultiplicity[s]/RealScalarList[[s,3,i]]];
								];
								(* Adjoint Representation *)
								If[RealScalarList[[s,3,i]] === Sqr[ListGauge[[i,3]]] - 1,
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> SMultiplicity[s]/RealScalarList[[s,3,i]] ListGauge[[i,3]]];
								];
								(* Symmetric Representation *)
								If[RealScalarList[[s,3,i]] === 1/2 ListGauge[[i,3]] (ListGauge[[i,3]] + 1),
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> (ListGauge[[i,3]] + 2)(ListGauge[[i,3]] - 1)/ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> SMultiplicity[s]/RealScalarList[[s,3,i]] (1/2 ListGauge[[i,3]] + 1)];
								];
								(* Antisymmetric Representation *)
								If[RealScalarList[[s,3,i]] === 1/2 ListGauge[[i,3]] (ListGauge[[i,3]] - 1),
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> (ListGauge[[i,3]] - 2)(ListGauge[[i,3]] + 1)/ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> SMultiplicity[s]/RealScalarList[[s,3,i]] (1/2 ListGauge[[i,3]] - 1)];
								];
							];
						];
						(* SO(N) subgroup *)
						If[ListGauge[[i,2]] === SO,
							If[RealScalarList[[s,3,i]] === 1,
								subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 0];
								Continue[];,
								(* Fundamental Representation *)
								If[RealScalarList[[s,3,i]] === ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/4 (ListGauge[[i,3]] - 1)];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/2 SMultiplicity[s]/RealScalarList[[s,3,i]]];
								];
								(* Adjoint Representation *)
								If[RealScalarList[[s,3,i]] === 1/2 ListGauge[[i,3]](ListGauge[[i,3]] - 1),
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/2 (ListGauge[[i,3]] - 2)];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/2 (ListGauge[[i,3]] - 2) SMultiplicity[s]/RealScalarList[[s,3,i]]];
								];
								(* Symmetric Representation *)
								If[RealScalarList[[s,3,i]] === 1/2 ListGauge[[i,3]](ListGauge[[i,3]] + 1) - 1,
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/2 ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/2 (ListGauge[[i,3]] + 2) SMultiplicity[s]/RealScalarList[[s,3,i]]];
								];
							];
						];
						(* Sp(2N) subgroup *)
						If[ListGauge[[i,2]] === Sp,
							If[RealScalarList[[s,3,i]] === 1,
								subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 0];
								Continue[];,
								(* Fundamental Representation *)
								If[RealScalarList[[s,3,i]] === ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/4 (ListGauge[[i,3]] + 1)];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/2 SMultiplicity[s]/RealScalarList[[s,3,i]]];
								];
								(* Adjoint Representation *)
								If[RealScalarList[[s,3,i]] === 1/2 ListGauge[[i,3]](ListGauge[[i,3]] + 1),
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> (1/2 ListGauge[[i,3]] + 1)];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> (1/2 ListGauge[[i,3]] + 1) SMultiplicity[s]/RealScalarList[[s,3,i]]];
								];
								(* Antisymmetric Representation *)
								If[RealScalarList[[s,3,i]] === 1/2 (ListGauge[[i,3]]-2)(ListGauge[[i,3]] + 1),
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> (1/2 ListGauge[[i,3]])];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> (1/2 ListGauge[[i,3]] - 1) SMultiplicity[s]/RealScalarList[[s,3,i]]];
								];
							];
						];
						(* U(1) subgroup *)
						If[ListGauge[[i,2]] === U && ListGauge[[i,3]] === 1,
							subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]->Sqr[RealScalarList[[s,3,i]]]];
							subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]->Sqr[RealScalarList[[s,3,i]]] SMultiplicity[s]];
						];
					];
				];
			];
			(* Gauge-Yukawa Invariants *)
			assHold=$Assumptions;
			$Assumptions=$Assumptions&&And@@Function[{x}, Element[sIdx[x],Integers]&&(sIdx[x]>0)]/@Range[NumberOfSubgroups+2];
			For[f=1, f<=Length[WeylFermionList], f++,
				For[sIdx[0]=1, sIdx[0]<=Length[RealScalarList], sIdx[0]++,
					If[
						WeylFermionList != {} && ListYukawa != {} && RealScalarList != {},
						Y4Hold[f, sIdx[0]] =
							ContractSum@@Join[
								{
									SolveTrace3[Delt[f], Yuk[sIdx[0]], adj[Yuk[sIdx[0]]], Prepend[
										Function[{x}, {sIdx[2+x],sIdx[2+x],sIdx[2+x]}]/@Range[NumberOfSubgroups],
										{sIdx[1],sIdx[2],sIdx[1],sIdx[2],sIdx[1],sIdx[2]}
									]],
									{sIdx[1], 1, RealScalarList[[sIdx[0],2,1]]},
									{sIdx[2], 1, RealScalarList[[sIdx[0],2,2]]}
								},
								Function[{x}, {sIdx[2+x],1,SMultiplicity[sIdx[0],x]}]/@Range[NumberOfSubgroups]
							];,
						Y4Hold[f, sIdx[0]] = 0;
					];
				];
			];
			For[i=1, i<=NumberOfSubgroups, i++,
				For[s=1, s<=Length[RealScalarList], s++,
					subInvariants = Append[subInvariants, Y2[RealScalarList[[s,1]], ListGauge[[i,1]]]->(1/d[ListGauge[[i,1]]] Sum[SimplifyProduct[Y4Hold[f,s]], {f,1,Length[WeylFermionList]}])];
					subInvariants = Append[subInvariants, Y4[RealScalarList[[s,1]], ListGauge[[i,1]]]->(1/d[ListGauge[[i,1]]] Sum[C2[WeylFermionList[[f,1]], ListGauge[[i,1]]] SimplifyProduct[Y4Hold[f,s]], {f,1,Length[WeylFermionList]}])];
					For[ii=1, ii<=NumberOfSubgroups, ii++,
						subInvariants = Append[subInvariants, Y6[RealScalarList[[s,1]], ListGauge[[i,1]], ListGauge[[ii,1]]]->(1/d[ListGauge[[i,1]]] Sum[C2[WeylFermionList[[f,1]], ListGauge[[i,1]]] C2[WeylFermionList[[f,1]], ListGauge[[ii,1]]] SimplifyProduct[Y4Hold[f,s]], {f,1,Length[WeylFermionList]}])];
					];
				];
			];
			$Assumptions=assHold;
		];

		(* Kronecker delta for arbitray list of arguments*)
		TensorDelta[{},{}] := 1;
		TensorDelta[a_List, b_List] := KroneckerDelta[a[[1]], b[[1]]] TensorDelta[Delete[a,1], Delete[b,1]];
		(* Delta symbol for complex scalars corresponding to real/imaginary parts *)
		ComplexDelta[a_, b_] := If[(MatchQ[a, Im[_]] || MatchQ[a, Re[_]]) && (MatchQ[b, Im[_]] || MatchQ[b, Re[_]]) && (a[[1]] === b[[1]]), 1, 0 ];

		(* Matrix multiplication and traces for Yukawas *)
		subProd := Dispatch[{
			prod[a___, b_ + c_, d___]:>(prod[a, b, d] + prod[a, c, d]),
			prod[][ii1_,ii2_]:>KroneckerDelta[ii1,ii2],
			prod[]:>1,
			prod[a_][ii1_,ii2_]:>a[ii1,ii2],
			prod[a___, prod[b___], c___]:>prod[a, b, c],
			prod[a___, n_, b___]:>(n prod[a,b])/; NumberQ[n],
			prod[a___, n_ c_, b___]:>(n prod[a,c,b])/; NumberQ[n],
			prod[a___, 0, b___]:>0,
			tr[a___, b_ + c_, d___]:>(tr[a, b, d] + tr[a, c, d]),
			tr[a___, n_, b___]:>(n tr[a,b])/; NumberQ[n],
			tr[a___, n_ c_, b___]:>(n tr[a,c,b]) /; NumberQ[n],
			tr[a___, 0, b___]:>0,
			tr[a___, prod[b___], c___]:>tr[a,b,c],
			adj[tr[a___]]:>tr[adj[a]],
			adj[prod[a___]]:>prod[adj[a]],
			prod[adj[a__,b__]]:>prod[adj[b],adj[a]],
			tr[adj[a___,b___]]:>tr[adj[b],adj[a]],
			adj[n_ a_]:> (Conjugate[n] adj[a]) /; NumberQ[n],
			prod[a___, tr[b___], c___]:>(tr[b] prod[a,c]),
			tr[a___ prod[b___]]:>(a tr[b]),
			adj[a_][i1_, i2_]:>adj[a[i2, i1]],
			adj[adj[a_]]:>a,
			adj[a_+ b_] :> (adj[a] + adj[b]),
			adj[0]->0
		}];

		(* replaces Yukawas and other Invariants in Fermion traces and products *)
		subYuk1 := Dispatch[{
			adj[Yuk[a_][i1_, i2_]] :> AdjYukMat[[a, i2, i1]],
			Yuk[a_][i1_, i2_] :> YukMat[[a, i1, i2]],
			Delt[ii_][i1_,i2_] :> If[AdjWeylFermionList[[i1,2]] == ii && AdjWeylFermionList[[i1,2]] == ii && AdjWeylFermionList[[i1,3]] == i2, Delta[ii], 0]
		}];
		subYuk2 := Dispatch[{
			adj[transpose[yuk[pos_]]]:>Join[
				{
					{
						conj[ListYukawa[[pos,1]]]//.subProd,
						Evaluate[Refine[Conjugate[ListYukawa[[pos,6]][#1,#2,#3,#4]]]]&,
						If[ListYukawa[[pos, 2]] > Length[RealScalarList], 1, RealScalarList[[ListYukawa[[pos, 2]], 2, 1]]],
						If[ListYukawa[[pos, 2]] > Length[RealScalarList], 1, RealScalarList[[ListYukawa[[pos, 2]], 2, 2]]],
						WeylFermionList[[AdjWeylFermionList[[ListYukawa[[pos, 3]], 2]], 2]],
						WeylFermionList[[AdjWeylFermionList[[ListYukawa[[pos, 4]], 2]], 2]]

					}
				},
				Function[
					{x},
					Join[
						{Evaluate[Refine[Conjugate[ListYukawa[[pos, 5, x]][#1,#2,#3]]]]&},
						{SMultiplicity[ListYukawa[[pos, 2]], x], FMultiplicity[AdjWeylFermionList[[ListYukawa[[pos, 3]], 2]], x], FMultiplicity[AdjWeylFermionList[[ListYukawa[[pos, 4]], 2]], x]}
					]
				]/@Range[NumberOfSubgroups]
			],
			transpose[yuk[pos_]]:>Join[
				{
					{
						adj[conj[ListYukawa[[pos,1]]]]//.subProd,
						Evaluate[Refine[ListYukawa[[pos,6]][#1,#2,#4,#3]]]&,
						If[ListYukawa[[pos, 2]] > Length[RealScalarList], 1, RealScalarList[[ListYukawa[[pos, 2]], 2, 1]]],
						If[ListYukawa[[pos, 2]] > Length[RealScalarList], 1, RealScalarList[[ListYukawa[[pos, 2]], 2, 2]]],
						WeylFermionList[[AdjWeylFermionList[[ListYukawa[[pos, 4]], 2]], 2]],
						WeylFermionList[[AdjWeylFermionList[[ListYukawa[[pos, 3]], 2]], 2]]

					}
				},
				Function[
					{x},
					Join[
						{Evaluate[Refine[ListYukawa[[pos, 5, x]][#1,#3,#2]]]&},
						{SMultiplicity[ListYukawa[[pos, 2]], x], FMultiplicity[AdjWeylFermionList[[ListYukawa[[pos, 4]], 2]], x], FMultiplicity[AdjWeylFermionList[[ListYukawa[[pos, 3]], 2]], x]}
					]
				]/@Range[NumberOfSubgroups]
			],
			adj[yuk[pos_]]:>Join[
				{
					{
						adj[ListYukawa[[pos,1]]]//.subProd,
						Evaluate[Refine[Conjugate[ListYukawa[[pos,6]][#1,#2,#4,#3]]]]&,
						If[ListYukawa[[pos, 2]] > Length[RealScalarList], 1, RealScalarList[[ListYukawa[[pos, 2]], 2, 1]]],
						If[ListYukawa[[pos, 2]] > Length[RealScalarList], 1, RealScalarList[[ListYukawa[[pos, 2]], 2, 2]]],
						WeylFermionList[[AdjWeylFermionList[[ListYukawa[[pos, 4]], 2]], 2]],
						WeylFermionList[[AdjWeylFermionList[[ListYukawa[[pos, 3]], 2]], 2]]
					}
				},
				Function[
					{x},
					Join[
						{Evaluate[Refine[Conjugate[ListYukawa[[pos, 5, x]][#1,#3,#2]]]]&},
						{SMultiplicity[ListYukawa[[pos, 2]], x], FMultiplicity[AdjWeylFermionList[[ListYukawa[[pos, 4]], 2]], x], FMultiplicity[AdjWeylFermionList[[ListYukawa[[pos, 3]], 2]], x]}
					]
				]/@Range[NumberOfSubgroups]
			],
			yuk[pos_]:>Join[
				{
					{
						ListYukawa[[pos,1]]//.subProd,
						ListYukawa[[pos,6]],
						If[ListYukawa[[pos, 2]] > Length[RealScalarList], 1, RealScalarList[[ListYukawa[[pos, 2]], 2, 1]]],
						If[ListYukawa[[pos, 2]] > Length[RealScalarList], 1, RealScalarList[[ListYukawa[[pos, 2]], 2, 2]]],
						WeylFermionList[[AdjWeylFermionList[[ListYukawa[[pos, 3]], 2]], 2]],
						WeylFermionList[[AdjWeylFermionList[[ListYukawa[[pos, 4]], 2]], 2]]
					}

				},
				Function[
					{x},
					Join[
						{ListYukawa[[pos, 5, x]]},
						{SMultiplicity[ListYukawa[[pos, 2]], x], FMultiplicity[AdjWeylFermionList[[ListYukawa[[pos, 3]], 2]], x], FMultiplicity[AdjWeylFermionList[[ListYukawa[[pos, 4]], 2]], x]}
					]
				]/@Range[NumberOfSubgroups]
			],
			Delta[ii_] :> Join[
				{{del[ii], Mat[1]&, 1, 1, WeylFermionList[[ii,2]], WeylFermionList[[ii,2]]}},
				Function[{x}, {KroneckerDelta[#2,#3]&, 1, FMultiplicity[ii,x], FMultiplicity[ii,x]}]/@Range[NumberOfSubgroups]
			]
		}];

		(* substitution rule for scalar sector *)
		subQuart1 := Dispatch[{Quartic[a_, b_, c_, d_] :> QuartMat[[a,b,c,d]]}];
		subQuart2 := Dispatch[{
			Quart[q_] :> Join[
				{
					{
						ListQuarticSym[[q,1]], ListQuarticSym[[q,7]],
						If[ListQuarticSym[[q,2]] > Length[RealScalarList], 1, RealScalarList[[ListQuarticSym[[q,2]], 2, 1]]],
						If[ListQuarticSym[[q,2]] > Length[RealScalarList], 1, RealScalarList[[ListQuarticSym[[q,2]], 2, 2]]],
						If[ListQuarticSym[[q,3]] > Length[RealScalarList], 1, RealScalarList[[ListQuarticSym[[q,3]], 2, 1]]],
						If[ListQuarticSym[[q,3]] > Length[RealScalarList], 1, RealScalarList[[ListQuarticSym[[q,3]], 2, 2]]],
						If[ListQuarticSym[[q,4]] > Length[RealScalarList], 1, RealScalarList[[ListQuarticSym[[q,4]], 2, 1]]],
						If[ListQuarticSym[[q,4]] > Length[RealScalarList], 1, RealScalarList[[ListQuarticSym[[q,4]], 2, 2]]],
						If[ListQuarticSym[[q,5]] > Length[RealScalarList], 1, RealScalarList[[ListQuarticSym[[q,5]], 2, 1]]],
						If[ListQuarticSym[[q,5]] > Length[RealScalarList], 1, RealScalarList[[ListQuarticSym[[q,5]], 2, 2]]]}
				},
				Function[{x}, {ListQuarticSym[[q,6,x]], SMultiplicity[ListQuarticSym[[q,2]], x], SMultiplicity[ListQuarticSym[[q,3]], x], SMultiplicity[ListQuarticSym[[q,4]], x], SMultiplicity[ListQuarticSym[[q,5]], x]}]/@Range[NumberOfSubgroups]
			]
		}];



		subScalarInvariants := Dispatch[{
			\[CapitalLambda]2[pa_, pb_, pc_, pd_] :> Block[
				{ss1, ss2, assHold, sum, x, x2},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[ contr, 
							ContractSum@@Join[
								{
									contr,
									{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
									{ss1[2], 1, RealScalarList[[ss1[0],2,2]]},
									{ss2[1], 1, RealScalarList[[ss2[0],2,1]]},
									{ss2[2], 1, RealScalarList[[ss2[0],2,2]]}
								},
								Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
							]
						],
						SolveSProd2[
							Quartic[pa[[1]], pb[[1]], ss1[0], ss2[0]],
							Quartic[ss1[0], ss2[0], pc[[1]], pd[[1]]],
							Prepend[
								Function[{x2}, {pa[[3+x2]], pb[[3+x2]], ss1[2+x2], ss2[2+x2],  ss1[2+x2], ss2[2+x2], pc[[3+x2]], pd[[3+x2]]}]/@Range[NumberOfSubgroups],
								{pa[[2]], pa[[3]], pb[[2]], pb[[3]], ss1[1], ss1[2], ss2[1], ss2[2], ss1[1], ss1[2], ss2[1], ss2[2], pc[[2]], pc[[3]], pd[[2]], pd[[3]]}
							]
						]
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]}
				];
				$Assumptions = assHold;
				sum
			],
			H[pa_, pb_, pc_, pd_] :> SolveTrace4[
				Yuk[pa[[1]]], adj[Yuk[pb[[1]]]], Yuk[pc[[1]]], adj[Yuk[pd[[1]]]],
				Prepend[
					Function[{x}, {pa[[x+3]], pb[[x+3]], pc[[x+3]], pd[[x+3]]}]/@Range[NumberOfSubgroups],
					{pa[[2]], pa[[3]], pb[[2]], pb[[3]], pc[[2]], pc[[3]], pd[[2]], pd[[3]]}
				]
			],
			\[CapitalLambda]Y[pa_, pb_, pc_, pd_] :> Block[
				{ss1, assHold, sum, x},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ContractSum@@Join[
						{
							1/2 (
								SolveTrace2[Yuk[pa[[1]]], adj[Yuk[ss1[0]]], Prepend[Function[{x}, {pa[[3+x]], ss1[2+x]}]/@Range[NumberOfSubgroups], {pa[[2]], pa[[3]], ss1[1], ss1[2]}]] +
								SolveTrace2[Yuk[ss1[0]], adj[Yuk[pa[[1]]]], Prepend[Function[{x}, {ss1[2+x], pa[[3+x]]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], pa[[2]], pa[[3]]}]]
							) BetaQuartic[ss1[0], pb[[1]], pc[[1]], pd[[1]], ss1/@Range[NumberOfSubgroups+2], pb[[2;;]], pc[[2;;]], pd[[2;;]], 0],
							{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
							{ss1[2], 1, RealScalarList[[ss1[0],2,2]]}
						},
						Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
					],
					{ss1[0], 1, Length[RealScalarList]}
				];
				$Assumptions = assHold;
				sum
			],
			\[CapitalLambda]S[gaug_][pa_, pb_, pc_, pd_] :> ReleaseHold[
				BetaQuartic[pa[[1]], pb[[1]], pc[[1]], pd[[1]], pa[[2;;]], pb[[2;;]], pc[[2;;]], pd[[2;;]], 0] Hold[
					If[pa[[1]] > Length[RealScalarList], 0, C2[RealScalarList[[pa[[1]],1]], ListGauge[[gaug,1]]]] +
					If[pb[[1]] > Length[RealScalarList], 0, C2[RealScalarList[[pb[[1]],1]], ListGauge[[gaug,1]]]] +
					If[pc[[1]] > Length[RealScalarList], 0, C2[RealScalarList[[pc[[1]],1]], ListGauge[[gaug,1]]]] +
					If[pd[[1]] > Length[RealScalarList], 0, C2[RealScalarList[[pd[[1]],1]], ListGauge[[gaug,1]]]]
				]
			],
			As[gaug1_, gaug2_][a_, b_, c_, d_] :> Block[
				{ind1, ind2, ind1L, ind2L, sum, x},
				sum = 0;
				ind1L = ind1/@Range[0,NumberOfSubgroups+2];
				ind2L = ind2/@Range[0,NumberOfSubgroups+2];
				For[ind1[0]=1, ind1[0]<=Length[RealScalarList], ind1[0]++,
					For[ind2[0]=1, ind2[0]<=Length[RealScalarList], ind2[0]++,
						sum += ContractSum@@Join[
							{\[CapitalLambda][gaug1][a, c, ind1L, ind2L] \[CapitalLambda][gaug2][ind1L, ind2L, b, d] + \[CapitalLambda][gaug1][a, ind1L, ind2L, d] \[CapitalLambda][gaug2][ind1L, b, c, ind2L],
							{ind1[1], 1, RealScalarList[[ind1[0], 2,1]]},
							{ind2[1], 1, RealScalarList[[ind2[0], 2,1]]},
							{ind1[2], 1, RealScalarList[[ind1[0], 2,2]]},
							{ind2[2], 1, RealScalarList[[ind2[0], 2,2]]}},
							Function[{x}, {ind1[x+2], 1, SMultiplicity[ind1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ind2[x+2], 1, SMultiplicity[ind2[0], x]}]/@Range[NumberOfSubgroups]
						]//.sub\[CapitalLambda]S;
					];
				];
				sum
			],
			Y2S[pa_List, pb_List] :> 0 /; (pa[[1]] > Length[RealScalarList] || pb[[1]] > Length[RealScalarList]),
			Y2S[pa_, pb_] :> 1/2 (
				SolveTrace2[adj[Yuk[pa[[1]]]], Yuk[pb[[1]]], Prepend[Function[{x}, {pa[[3+x]], pb[[3+x]]}]/@Range[NumberOfSubgroups], {pa[[2]], pa[[3]], pb[[2]], pb[[3]]}]] +
				SolveTrace2[adj[Yuk[pb[[1]]]], Yuk[pa[[1]]], Prepend[Function[{x}, {pb[[3+x]], pa[[3+x]]}]/@Range[NumberOfSubgroups], {pb[[2]], pb[[3]], pa[[2]], pa[[3]]}]]
			),
			\[CapitalLambda]2S[pa_List, pb_List] :> 0 /; (pa[[1]] > Length[RealScalarList] || pb[[1]] > Length[RealScalarList]),
			\[CapitalLambda]2S[pa_, pb_] :> Block[
				{ss1, ss2, ss3, assHold, sum, x, x2},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)&&Element[ss3[x],Integers]&&(ss3[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[ contr, ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0],2,2]]},
								{ss2[1], 1, RealScalarList[[ss2[0],2,1]]},
								{ss2[2], 1, RealScalarList[[ss2[0],2,2]]},
								{ss3[1], 1, RealScalarList[[ss3[0],2,1]]},
								{ss3[2], 1, RealScalarList[[ss3[0],2,2]]}
							},
							Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss3[x+2], 1, SMultiplicity[ss3[0], x]}]/@Range[NumberOfSubgroups]
						]],
						SolveSProd2[
							Quartic[pa[[1]], ss1[0], ss2[0], ss3[0]],
							Quartic[pb[[1]], ss1[0], ss2[0], ss3[0]],
							Prepend[
								Function[{x2}, {pa[[3+x2]], ss1[2+x2], ss2[2+x2], ss3[2+x2], pb[[3+x2]], ss1[2+x2], ss2[2+x2], ss3[2+x2]}]/@Range[NumberOfSubgroups],
								{pa[[2]], pa[[3]], ss1[1], ss1[2], ss2[1], ss2[2], ss3[1], ss3[2], pb[[2]], pb[[3]], ss1[1], ss1[2], ss2[1], ss2[2], ss3[1], ss3[2]}
							]
						]
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]},
					{ss3[0], 1, Length[RealScalarList]}
				];
				$Assumptions = assHold;
				Sqr[24]/6 sum
			],
			\[CapitalLambda]2SY[pa_, pi_, pj_] :> Block[
				{ss1, ss2, ss3, ss4, assHold, sum, x, x2},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)&&Element[ss3[x],Integers]&&(ss3[x]>0)&&Element[ss4[x],Integers]&&(ss4[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[ contr, ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0],2,2]]},
								{ss2[1], 1, RealScalarList[[ss2[0],2,1]]},
								{ss2[2], 1, RealScalarList[[ss2[0],2,2]]},
								{ss3[1], 1, RealScalarList[[ss3[0],2,1]]},
								{ss3[2], 1, RealScalarList[[ss3[0],2,2]]},
								{ss4[1], 1, RealScalarList[[ss4[0],2,1]]},
								{ss4[2], 1, RealScalarList[[ss4[0],2,2]]}
							},
							Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss3[x+2], 1, SMultiplicity[ss3[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss4[x+2], 1, SMultiplicity[ss4[0], x]}]/@Range[NumberOfSubgroups]
						]],
						SolveSProd2[
							Quartic[pa[[1]], ss1[0], ss2[0], ss3[0]],
							Quartic[ss4[0] , ss1[0], ss2[0], ss3[0]],
							Prepend[
								Function[{x2}, {pa[[3+x2]], ss1[2+x2], ss2[2+x2], ss3[2+x2], ss4[2+x2], ss1[2+x2], ss2[2+x2], ss3[2+x2]}]/@Range[NumberOfSubgroups],
								{pa[[2]], pa[[3]], ss1[1], ss1[2], ss2[1], ss2[2], ss3[1], ss3[2], ss4[1], ss4[2], ss1[1], ss1[2], ss2[1], ss2[2], ss3[1], ss3[2]}
							]
						] BetaYukawa[ss4[0], pi[[1]], pj[[1]], ss4/@Range[1, NumberOfSubgroups+2], pi[[2;;]], pj[[2;;]], 0]
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]},
					{ss3[0], 1, Length[RealScalarList]},
					{ss4[0], 1, Length[RealScalarList]}
				];
				$Assumptions = assHold;
				Sqr[24]/6 sum
			],
			\[CapitalLambda]2S\[Lambda][pa_, pb_, pc_, pd_] :> Block[
				{ss1, ss2, ss3, ss4, assHold, sum, x, x2},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)&&Element[ss3[x],Integers]&&(ss3[x]>0)&&Element[ss4[x],Integers]&&(ss4[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = 1/6 Sum[
					ApplyDistribute[
						Function[ contr,
							ContractSum@@Join[
								{
									contr,
									{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
									{ss1[2], 1, RealScalarList[[ss1[0],2,2]]},
									{ss2[1], 1, RealScalarList[[ss2[0],2,1]]},
									{ss2[2], 1, RealScalarList[[ss2[0],2,2]]},
									{ss3[1], 1, RealScalarList[[ss3[0],2,1]]},
									{ss3[2], 1, RealScalarList[[ss3[0],2,2]]},
									{ss4[1], 1, RealScalarList[[ss4[0],2,1]]},
									{ss4[2], 1, RealScalarList[[ss4[0],2,2]]}
								},
								Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss3[x+2], 1, SMultiplicity[ss3[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss4[x+2], 1, SMultiplicity[ss4[0], x]}]/@Range[NumberOfSubgroups]
							]
						], SolveSProd3[
							Quartic[pa[[1]], ss1[0], ss2[0], ss3[0]],
							Quartic[ss4[0], ss1[0], ss2[0], ss3[0]],
							Quartic[ss4[0], pb[[1]], pc[[1]], pd[[1]]],
									Prepend[
								Function[{x2}, {pa[[3+x2]], ss1[2+x2], ss2[2+x2], ss3[2+x2], ss4[2+x2], ss1[2+x2], ss2[2+x2], ss3[2+x2], ss4[2+x2], pb[[3+x2]], pc[[3+x2]], pd[[3+x2]]}]/@Range[NumberOfSubgroups],
								{pa[[2]], pa[[3]], ss1[1], ss1[2], ss2[1], ss2[2], ss3[1], ss3[2], ss4[1], ss4[2], ss1[1], ss1[2], ss2[1], ss2[2], ss3[1], ss3[2], ss4[1], ss4[2], pb[[2]], pb[[3]], pc[[2]], pc[[3]], pd[[2]], pd[[3]]}
							]
						]
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]},
					{ss3[0], 1, Length[RealScalarList]},
					{ss4[0], 1, Length[RealScalarList]}
				];
				$Assumptions = assHold;
				sum
			],
			H2S[pa_List, pb_List] :> 0 /; (pa[[1]] > Length[RealScalarList] || pb[[1]] > Length[RealScalarList]),
			H2S[pa_, pb_] :> Block[
				{ss,x,x2,sum,assHold},
				assHold = $Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss[x],Integers]&&(ss[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = 1/2 Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss[1], 1, RealScalarList[[ss[0], 2, 1]]},
									{ss[2], 1, RealScalarList[[ss[0], 2, 2]]}
								},
								Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups]
							]
						], (
							SolveTrace4[
								Yuk[pa[[1]]], adj[Yuk[pb[[1]]]], Yuk[ss[0]], adj[Yuk[ss[0]]],
								Prepend[Function[{x2}, {pa[[3+x2]], pb[[x2+3]], ss[x2+2], ss[x2+2]}]/@Range[NumberOfSubgroups], {pa[[2]], pa[[3]], pb[[2]], pb[[3]], ss[1], ss[2], ss[1], ss[2]}]
							] +
							SolveTrace4[
								Yuk[pb[[1]]], adj[Yuk[pa[[1]]]], Yuk[ss[0]], adj[Yuk[ss[0]]],
								Prepend[Function[{x2}, {pb[[3+x2]], pa[[x2+3]], ss[x2+2], ss[x2+2]}]/@Range[NumberOfSubgroups], {pb[[2]], pb[[3]], pa[[2]], pa[[3]], ss[1], ss[2], ss[1], ss[2]}]
							]
						)
					],
					{ss[0], 1, Length[RealScalarList]}
				]/.subKron;
				$Assumptions=assHold;
				sum
			],
			H2S\[Lambda][pa_, pb_, pc_, pd_] :> Block[
				{ss,ss2,x,x2,sum,assHold},
				assHold = $Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss[x],Integers]&&(ss[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = 1/2 Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss[1], 1, RealScalarList[[ss[0], 2, 1]]},
									{ss[2], 1, RealScalarList[[ss[0], 2, 2]]},
									{ss2[1], 1, RealScalarList[[ss2[0], 2, 1]]},
									{ss2[2], 1, RealScalarList[[ss2[0], 2, 2]]}
								},
								Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
							]
						], (
							SolveTrace4[
								Yuk[pa[[1]]], adj[Yuk[ss2[0]]], Yuk[ss[0]], adj[Yuk[ss[0]]],
								Prepend[Function[{x2}, {pa[[3+x2]], ss2[x2+2], ss[x2+2], ss[x2+2]}]/@Range[NumberOfSubgroups], {pa[[2]], pa[[3]], ss2[1], ss2[2], ss[1], ss[2], ss[1], ss[2]}]
							] +
							SolveTrace4[
								Yuk[ss2[0]], adj[Yuk[pa[[1]]]], Yuk[ss[0]], adj[Yuk[ss[0]]],
								Prepend[Function[{x2}, {ss2[2+x2], pa[[x2+3]], ss[x2+2], ss[x2+2]}]/@Range[NumberOfSubgroups], {ss2[1], ss2[2], pa[[2]], pa[[3]], ss[1], ss[2], ss[1], ss[2]}]
							]
						) BetaQuartic[ss2[0], pb[[1]], pc[[1]], pd[[1]], ss2/@Range[NumberOfSubgroups+2], pb[[2;;]], pc[[2;;]], pd[[2;;]], 0]
					],
					{ss[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]}
				]/.subKron;
				$Assumptions=assHold;
				sum
			],
			H2SY[pa_, pi_, pj_] :> Block[
				{ss,ss2,x,x2,sum,assHold},
				assHold = $Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss[x],Integers]&&(ss[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = 1/2 Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss[1], 1, RealScalarList[[ss[0], 2, 1]]},
									{ss[2], 1, RealScalarList[[ss[0], 2, 2]]},
									{ss2[1], 1, RealScalarList[[ss2[0], 2, 1]]},
									{ss2[2], 1, RealScalarList[[ss2[0], 2, 2]]}
								},
								Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
							]
						], (
							SolveTrace4[
								Yuk[pa[[1]]], adj[Yuk[ss2[0]]], Yuk[ss[0]], adj[Yuk[ss[0]]],
								Prepend[Function[{x2}, {pa[[3+x2]], ss2[x2+2], ss[x2+2], ss[x2+2]}]/@Range[NumberOfSubgroups], {pa[[2]], pa[[3]], ss2[1], ss2[2], ss[1], ss[2], ss[1], ss[2]}]
							] +
							SolveTrace4[
								Yuk[ss2[0]], adj[Yuk[pa[[1]]]], Yuk[ss[0]], adj[Yuk[ss[0]]],
								Prepend[Function[{x2}, {ss2[2+x2], pa[[x2+3]], ss[x2+2], ss[x2+2]}]/@Range[NumberOfSubgroups], {ss2[1],ss2[2], pa[[2]], pa[[3]], ss[1], ss[2], ss[1], ss[2]}]
							]
						) BetaYukawa[ss2[0], pi[[1]], pj[[1]], ss2/@Range[1, NumberOfSubgroups+2], pi[[2;;]], pj[[2;;]], 0]
					],
					{ss[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]}
				]/.subKron;
				$Assumptions=assHold;
				sum
			],
			Hbar2S[pa_List, pb_List] :> 0 /; (pa[[1]] > Length[RealScalarList] || pb[[1]] > Length[RealScalarList]),
			Hbar2S[pa_, pb_] :> Block[
				{ss,x,x2,sum,assHold},
				assHold = $Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss[x],Integers]&&(ss[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = 1/2 Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss[1], 1, RealScalarList[[ss[0], 2, 1]]},
									{ss[2], 1, RealScalarList[[ss[0], 2, 2]]}
								},
								Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups]
							]
						], (
							SolveTrace4[
								Yuk[pa[[1]]], adj[Yuk[ss[0]]], Yuk[pb[[1]]], adj[Yuk[ss[0]]],
								Prepend[Function[{x2}, {pa[[3+x2]], ss[x2+2], pb[[x2+3]], ss[x2+2]}]/@Range[NumberOfSubgroups], {pa[[2]], pa[[3]], ss[1], ss[2], pb[[2]], pb[[3]], ss[1], ss[2]}]
										] +
							SolveTrace4[
								adj[Yuk[pa[[1]]]], Yuk[ss[0]], adj[Yuk[pb[[1]]]], Yuk[ss[0]],
								Prepend[Function[{x2}, {pa[[3+x2]], ss[x2+2], pb[[x2+3]], ss[x2+2]}]/@Range[NumberOfSubgroups], {pa[[2]], pa[[3]], ss[1], ss[2], pb[[2]], pb[[3]], ss[1], ss[2]}]
							]
						)
					],
					{ss[0], 1, Length[RealScalarList]}
				]/.subKron;
				$Assumptions=assHold;
				sum
			],
			Hbar2S\[Lambda][pa_, pb_, pc_, pd_] :> Block[
				{ss,ss2,x,x2,sum,assHold},
				assHold = $Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss[x],Integers]&&(ss[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = 1/2 Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss[1], 1, RealScalarList[[ss[0], 2, 1]]},
									{ss[2], 1, RealScalarList[[ss[0], 2, 2]]},
									{ss2[1], 1, RealScalarList[[ss2[0], 2, 1]]},
									{ss2[2], 1, RealScalarList[[ss2[0], 2, 2]]}
								},
								Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
							]
						], (
							SolveTrace4[
								Yuk[pa[[1]]], adj[Yuk[ss[0]]], Yuk[ss2[0]], adj[Yuk[ss[0]]],
								Prepend[Function[{x2}, {pa[[3+x2]], ss[x2+2], ss2[x2+2], ss[x2+2]}]/@Range[NumberOfSubgroups], {pa[[2]], pa[[3]], ss[1], ss[2], ss2[1], ss2[2], ss[1], ss[2]}]
							] +
							SolveTrace4[
								adj[Yuk[pa[[1]]]], Yuk[ss[0]], adj[Yuk[ss2[0]]], Yuk[ss[0]],
								Prepend[Function[{x2}, {pa[[3+x2]], ss[x2+2], ss2[x2+2], ss[x2+2]}]/@Range[NumberOfSubgroups], {pa[[2]], pa[[3]], ss[1], ss[2], ss2[1], ss2[2], ss[1], ss[2]}]
							]
						) BetaQuartic[ss2[0], pb[[1]], pc[[1]], pd[[1]], ss2/@Range[NumberOfSubgroups+2], pb[[2;;]], pc[[2;;]], pd[[2;;]], 0]
					],
					{ss[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]}
				]/.subKron;
				$Assumptions=assHold;
				sum
			],
			Hbar2SY[pa_, pi_, pj_] :> Block[
				{ss,ss2,x,x2,sum,assHold},
				assHold = $Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss[x],Integers]&&(ss[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = 1/2 Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss[1], 1, RealScalarList[[ss[0], 2, 1]]},
									{ss[2], 1, RealScalarList[[ss[0], 2, 2]]},
									{ss2[1], 1, RealScalarList[[ss2[0], 2, 1]]},
									{ss2[2], 1, RealScalarList[[ss2[0], 2, 2]]}
								},
								Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
							]
						], (
							SolveTrace4[
								Yuk[pa[[1]]], adj[Yuk[ss[0]]], Yuk[ss2[0]], adj[Yuk[ss[0]]],
								Prepend[Function[{x2}, {pa[[3+x2]], ss[x2+2], ss2[x2+2], ss[x2+2]}]/@Range[NumberOfSubgroups], {pa[[2]], pa[[3]], ss[1], ss[2], ss2[1], ss2[2], ss[1], ss[2]}]
										] +
							SolveTrace4[
								adj[Yuk[pa[[1]]]], Yuk[ss[0]], adj[Yuk[ss2[0]]], Yuk[ss[0]],
								Prepend[Function[{x2}, {pa[[3+x2]], ss[x2+2], ss2[x2+2], ss[x2+2]}]/@Range[NumberOfSubgroups], {pa[[2]], pa[[3]], ss[1], ss[2], ss2[1], ss2[2], ss[1], ss[2]}]
							]
						) BetaYukawa[ss2[0], pi[[1]], pj[[1]], ss2/@Range[1, NumberOfSubgroups+2], pi[[2;;]], pj[[2;;]], 0]
					],
					{ss[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]}
				]/.subKron;
				$Assumptions=assHold;
				sum
			],
			Y2FS[pa_List, pb_List] :> 0 /; (pa[[1]] > Length[RealScalarList] || pb[[1]] > Length[RealScalarList]),
			Y2FS[pa_, pb_] :> Block[
				{ff,fHold,x,ii},
				For[ff=1, ff<=Length[WeylFermionList], ff++,
					fHold[ff] = 1/2 (
						SolveTrace3[Delt[ff], Yuk[pa[[1]]], adj[Yuk[pb[[1]]]], Prepend[Function[{x}, {1, pa[[x+3]], pb[[x+3]]}]/@Range[NumberOfSubgroups], {1, 1, pa[[2]], pa[[3]], pb[[2]], pb[[3]]}]] +
						SolveTrace3[Delt[ff], Yuk[pb[[1]]], adj[Yuk[pa[[1]]]], Prepend[Function[{x}, {1, pb[[x+3]], pa[[x+3]]}]/@Range[NumberOfSubgroups], {1, 1, pb[[2]], pb[[3]], pa[[2]], pa[[3]]}]]
					);
				];
				Sum[Sqr[ListGauge[[ii,1]]] C2[WeylFermionList[[ff,1]], ListGauge[[ii,1]]] fHold[ff] , {ff, 1, Length[WeylFermionList]}, {ii, 1, NumberOfSubgroups}]
			],
			Y2FSY[pa_, pi_, pj_, la_, li_, lj_] :> 0 /; (pa > Length[RealScalarList]),
			Y2FSY[pa_, pi_, pj_, la_, li_, lj_] :> Block[
				{ff,fHold,x,ii,ss,assHold},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss[x],Integers]&&(ss[x]>0)]/@Range[NumberOfSubgroups+2];
				For[ff=1, ff<=Length[WeylFermionList], ff++,
					fHold[ff] = Refine[Sum[
						5/2 ContractSum@@Join[
							{
								BetaYukawa[ss[0], pi, pj, ss/@Range[NumberOfSubgroups+2], li, lj, 0] (
									SolveTrace3[Delt[ff], Yuk[pa], adj[Yuk[ss[0]]], Prepend[Function[{x}, {1, la[[x+2]], ss[2+x]}]/@Range[NumberOfSubgroups], {1, 1, la[[1]], la[[2]], ss[1], ss[2]}]] +
									SolveTrace3[Delt[ff], Yuk[ss[0]], adj[Yuk[pa]], Prepend[Function[{x}, {1, ss[2+x], la[[x+2]]}]/@Range[NumberOfSubgroups], {1, 1, ss[1], ss[2], la[[1]], la[[2]]}]]
								),
								{ss[1], 1, RealScalarList[[ss[0], 2,1]]},
								{ss[2], 1, RealScalarList[[ss[0], 2,2]]}
							},
							Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups]
						],
						{ss[0], 1, Length[RealScalarList]}
					]];
				];
				$Assumptions=assHold;
				Sum[Sqr[ListGauge[[ii,1]]] C2[WeylFermionList[[ff,1]], ListGauge[[ii,1]]] fHold[ff] , {ff, 1, Length[WeylFermionList]}, {ii, 1, NumberOfSubgroups}]
			],
			Y2FSL[pa_, pb_, pc_, pd_] :> Block[
				{ff,fHold,x,ii,ss,assHold},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss[x],Integers]&&(ss[x]>0)]/@Range[NumberOfSubgroups+2];
				For[ff=1, ff<=Length[WeylFermionList], ff++,
					fHold[ff] = Refine[Sum[
						1/2 ContractSum@@Join[
							{
								BetaQuartic[ss[0], pb[[1]], pc[[1]], pd[[1]],  ss/@Range[NumberOfSubgroups+2], pb[[2;;]], pc[[2;;]], pd[[2;;]], 0] (
									SolveTrace3[Delt[ff], Yuk[pa[[1]]], adj[Yuk[ss[0]]], Prepend[Function[{x}, {1, pa[[x+3]], ss[2+x]}]/@Range[NumberOfSubgroups], {1, 1, pa[[2]], pa[[3]], ss[1], ss[2]}]] +
									SolveTrace3[Delt[ff], Yuk[ss[0]], adj[Yuk[pa[[1]]]], Prepend[Function[{x}, {1, ss[2+x], pa[[x+3]]}]/@Range[NumberOfSubgroups], {1, 1, ss[1], ss[2], pa[[2]], pa[[3]]}]]
								),
								{ss[1], 1, RealScalarList[[ss[0], 2,1]]},
								{ss[2], 1, RealScalarList[[ss[0], 2,2]]}
							},
							Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups]
						],
						{ss[0], 1, Length[RealScalarList]}
					]];
				];
				$Assumptions=assHold;
				Sum[Sqr[ListGauge[[ii,1]]] C2[WeylFermionList[[ff,1]], ListGauge[[ii,1]]] fHold[ff] , {ff, 1, Length[WeylFermionList]}, {ii, 1, NumberOfSubgroups}]
			],
			H2t[gauge_, pa_, pi_, pj_] :> Block[
				{sum, assHold,f1,f2},
				assHold = $Assumptions;
				$Assumptions=$Assumptions&&Element[scGenIdx,Integers]&&(scGenIdx>0)&&Element[scGenIdx2,Integers]&&(scGenIdx2>0)&&(And@@(Function[{x},Element[scGaugeIdx[x],Integers]&&(scGaugeIdx[x]>0)&&Element[ff1[x],Integers]&&(ff1[x]>0)&&Element[ff2[x],Integers]&&(ff2[x]>0)&&Element[ff3[x],Integers]&&(ff3[x]>0)&&Element[ff4[x],Integers]&&(ff4[x]>0)]/@Range[NumberOfSubgroups]));
				sum = Refine[Sum[
					(ReleaseHold[prod[Yuk[pa[[1]]][pi[[1]], f1], adj[Yuk[ss]][AdjWeylFermionList[[f1,3]], f2], Yuk[ss][AdjWeylFermionList[[f2,3]],pj[[1]]]] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk1 //.subProd]//.subYuk2 /.{
						prod[A_, B_, C_] :> ContractSum@@Join[
							{
								Refine[ContractSum[GetGenProd[{A,B,C}, {{pa[[2]], pa[[3]]}, {scGenIdx, scGenIdx2}, {scGenIdx, scGenIdx2}}, pi[[2]], pj[[2]]] //.subProd, {scGenIdx, 1, RealScalarList[[ss,2,1]]}, {scGenIdx2, 1, RealScalarList[[ss,2,2]]}]] Refine[Conjugate[
									\[CapitalLambda][gauge][pi, Join[{AdjWeylFermionList[[f2,3]],1},ff3/@Range[NumberOfSubgroups]], Join[{AdjWeylFermionList[[pi[[1]],3]], pi[[2]]}, ff1/@Range[NumberOfSubgroups]], Join[{f2,1},ff4/@Range[NumberOfSubgroups]]] //.sub\[CapitalLambda]F
								]] Times@@Function[{x}, A[[x+1, 1]][pa[[x+3]], ff1[x], ff2[x]] B[[x+1,1]][scGaugeIdx[x], ff2[x], ff3[x]] C[[x+1,1]][scGaugeIdx[x], ff4[x], pj[[x+2]]]]/@Range[NumberOfSubgroups]
							},
							Function[{x},{scGaugeIdx[x], 1, SMultiplicity[ss,x]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff1[x], 1, FMultiplicity[AdjWeylFermionList[[pi[[1]],2]],x]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff2[x], 1, FMultiplicity[AdjWeylFermionList[[f1,2]],x]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff3[x], 1, FMultiplicity[AdjWeylFermionList[[f2,2]],x]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff4[x], 1, FMultiplicity[AdjWeylFermionList[[f2,2]],x]}]/@Range[NumberOfSubgroups]
						]
					}) +
					(ReleaseHold[prod[Yuk[ss][pi[[1]], f1], adj[Yuk[ss]][AdjWeylFermionList[[f1,3]], f2], Yuk[pa[[1]]][AdjWeylFermionList[[f2,3]],pj[[1]]]] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk1 //.subProd]//.subYuk2 /.{
						prod[A_, B_, C_] :> ContractSum@@Join[
							{
								Refine[ContractSum[GetGenProd[{A,B,C}, {{scGenIdx, scGenIdx2}, {scGenIdx, scGenIdx2}, {pa[[2]], pa[[3]]}}, pi[[2]], pj[[2]]] //.subProd, {scGenIdx, 1, RealScalarList[[ss,2,1]]}, {scGenIdx2, 1, RealScalarList[[ss,2,2]]}]] Refine[
									\[CapitalLambda][gauge][Join[{AdjWeylFermionList[[f1,3]],1},ff1/@Range[NumberOfSubgroups]], Join[{AdjWeylFermionList[[pj[[1]],3]],pj[[2]]},ff4/@Range[NumberOfSubgroups]], Join[{f1, 1}, ff2/@Range[NumberOfSubgroups]], pj] //.sub\[CapitalLambda]F
								] Times@@Function[{x}, A[[x+1, 1]][scGaugeIdx[x], pi[[x+2]], ff1[x]] B[[x+1,1]][scGaugeIdx[x], ff2[x], ff3[x]] C[[x+1,1]][pa[[x+3]], ff3[x], ff4[x]]]/@Range[NumberOfSubgroups]
							},
							Function[{x},{scGaugeIdx[x], 1, SMultiplicity[ss,x]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff1[x], 1, FMultiplicity[AdjWeylFermionList[[f1,2]],x]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff2[x], 1, FMultiplicity[AdjWeylFermionList[[f1,2]],x]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff3[x], 1, FMultiplicity[AdjWeylFermionList[[f2,2]],x]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff4[x], 1, FMultiplicity[AdjWeylFermionList[[pj[[1]],2]],x]}]/@Range[NumberOfSubgroups]
						]
					}),
					{ss, 1, Length[RealScalarList]},
					{f1, 1, Length[AdjWeylFermionList]},
					{f2, 1, Length[AdjWeylFermionList]}
				]];
				$Assumptions=assHold;
				sum
			],
			\[CapitalLambda]bar3[pa_, pb_, pc_, pd_] :> Block[
				{ss1, ss2, ss3, ss4, assHold, sum, x, x2},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)&&Element[ss3[x],Integers]&&(ss3[x]>0)&&Element[ss4[x],Integers]&&(ss4[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[contr, ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0],2,2]]},
								{ss2[1], 1, RealScalarList[[ss2[0],2,1]]},
								{ss2[2], 1, RealScalarList[[ss2[0],2,2]]},
								{ss3[1], 1, RealScalarList[[ss3[0],2,1]]},
								{ss3[2], 1, RealScalarList[[ss3[0],2,2]]},
								{ss4[1], 1, RealScalarList[[ss4[0],2,1]]},
								{ss4[2], 1, RealScalarList[[ss4[0],2,2]]}
							},
							Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss3[x+2], 1, SMultiplicity[ss3[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss4[x+2], 1, SMultiplicity[ss4[0], x]}]/@Range[NumberOfSubgroups]
						]], SolveSProd3[
							Quartic[pa[[1]], pb[[1]], ss1[0], ss2[0]],
							Quartic[pc[[1]], ss1[0], ss3[0], ss4[0]],
							Quartic[pd[[1]], ss2[0], ss3[0], ss4[0]],
							Prepend[
								Function[{x2}, {pa[[3+x2]], pb[[3+x2]], ss1[2+x2], ss2[2+x2], pc[[3+x2]], ss1[2+x2], ss3[2+x2], ss4[2+x2], pd[[3+x2]], ss2[2+x2], ss3[2+x2], ss4[2+x2]}]/@Range[NumberOfSubgroups],
								{pa[[2]], pa[[3]], pb[[2]], pb[[3]], ss1[1], ss1[2], ss2[1], ss2[2], pc[[2]], pc[[3]], ss1[1], ss1[2], ss3[1], ss3[2], ss4[1], ss4[2], pd[[2]], pd[[3]], ss2[1], ss2[2], ss3[1], ss3[2], ss4[1], ss4[2]}
							]
						]
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]},
					{ss3[0], 1, Length[RealScalarList]},
					{ss4[0], 1, Length[RealScalarList]}
				];
				$Assumptions = assHold;
				sum
			],
			\[CapitalLambda]bar2Y[pa_, pb_, pc_, pd_] :> Block[
				{ss1, ss2, ss3, assHold, sum, x, x2, x3, x4},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)&&Element[ss3[x],Integers]&&(ss3[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[contr, ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0],2,2]]},
								{ss2[1], 1, RealScalarList[[ss2[0],2,1]]},
								{ss2[2], 1, RealScalarList[[ss2[0],2,2]]},
								{ss3[1], 1, RealScalarList[[ss3[0],2,1]]},
								{ss3[2], 1, RealScalarList[[ss3[0],2,2]]}
							},
							Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss3[x+2], 1, SMultiplicity[ss3[0], x]}]/@Range[NumberOfSubgroups]
						]], 
						1/2 SolveSProd2[
							Quartic[pa[[1]], pb[[1]], ss1[0], ss2[0]],
							Quartic[pc[[1]], pd[[1]], ss1[0], ss3[0]],
							Prepend[
								Function[{x2}, {pa[[3+x2]], pb[[3+x2]], ss1[2+x2], ss2[2+x2], pc[[3+x2]], pd[[3+x2]], ss1[2+x2], ss3[2+x2]}]/@Range[NumberOfSubgroups],
								{pa[[2]], pa[[3]], pb[[2]], pb[[3]], ss1[1], ss1[2], ss2[1], ss2[2], pc[[2]], pc[[3]], pd[[2]], pd[[3]], ss1[1], ss1[2], ss3[1], ss3[2]}
							]
						] (
							SolveTrace2[Yuk[ss2[0]], adj[Yuk[ss3[0]]], Prepend[Function[{x3}, {ss2[2+x3], ss3[2+x3]}]/@Range[NumberOfSubgroups], {ss2[1], ss2[2], ss3[1], ss3[2]}]] +
							SolveTrace2[Yuk[ss3[0]], adj[Yuk[ss2[0]]], Prepend[Function[{x3}, {ss3[2+x3], ss2[2+x3]}]/@Range[NumberOfSubgroups], {ss3[1], ss3[2], ss2[1], ss2[2]}]]
						)
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]},
					{ss3[0], 1, Length[RealScalarList]}
				];
				$Assumptions = assHold;
				sum
			],
			Hbar\[Lambda][pa_, pb_, pc_, pd_] :> Block[
				{ss1, ss2, sum, assHold, x},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
									{ss2[1], 1, RealScalarList[[ss1[0], 2,1]]},
									{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]},
									{ss2[2], 1, RealScalarList[[ss1[0], 2,2]]}
								},
								Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
							]
						],
						BetaQuartic[pa[[1]], pb[[1]], ss1[0], ss2[0], pa[[2;;]], pb[[2;;]], ss1/@Range[NumberOfSubgroups+2], ss2/@Range[NumberOfSubgroups+2], 0] (
							SolveTrace4[Yuk[pc[[1]]], adj[Yuk[ss1[0]]], Yuk[pd[[1]]], adj[Yuk[ss2[0]]], Prepend[Function[{x}, {pc[[3+x]], ss1[x+2], pd[[3+x]], ss2[2+x]}]/@Range[NumberOfSubgroups], {pc[[2]], pc[[3]], ss1[1], ss1[2], pd[[2]], pd[[3]], ss2[1], ss2[2]}]] +
							SolveTrace4[adj[Yuk[pc[[1]]]], Yuk[ss1[0]], adj[Yuk[pd[[1]]]], Yuk[ss2[0]], Prepend[Function[{x}, {pc[[3+x]], ss1[x+2], pd[[3+x]], ss2[2+x]}]/@Range[NumberOfSubgroups], {pc[[2]], pc[[3]], ss1[1], ss1[2], pd[[2]], pd[[3]], ss2[1], ss2[2]}]]
						)
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]}
				];
				$Assumptions=assHold;
				sum
			],
			HY[pa_, pb_, pc_, pd_] :> Block[
				{ss1, sum, assHold, x},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
									{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]}
								},
								Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
							]
						],
						SolveTrace6[
							adj[Yuk[ss1[0]]], Yuk[ss1[0]], adj[Yuk[pa[[1]]]], Yuk[pb[[1]]], adj[Yuk[pc[[1]]]], Yuk[pd[[1]]],
							Prepend[
								Function[{x}, {ss1[2+x], ss1[2+x], pa[[3+x]], pb[[3+x]], pc[[3+x]], pd[[3+x]]}]/@Range[NumberOfSubgroups],
								{ss1[1], ss1[2], ss1[1], ss1[2], pa[[2]], pa[[3]], pb[[2]], pb[[3]], pc[[2]], pc[[3]], pd[[2]], pd[[3]]}
							]
						]
					],
					{ss1[0], 1, Length[RealScalarList]}
				];
				$Assumptions=assHold;
				sum
			],
			HbarY[pa_, pb_, pc_, pd_] :> Block[
				{ss1, sum, assHold, x},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
									{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]}
								},
								Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
							]
						],
						SolveTrace6[
							Yuk[ss1[0]], adj[Yuk[pa[[1]]]], Yuk[ss1[0]], adj[Yuk[pb[[1]]]], Yuk[pc[[1]]], adj[Yuk[pd[[1]]]],
							Prepend[
								Function[{x}, {ss1[2+x], pa[[3+x]], ss1[2+x], pb[[3+x]], pc[[3+x]], pd[[3+x]]}]/@Range[NumberOfSubgroups],
								{ss1[1], ss1[2], pa[[2]], pa[[3]], ss1[1], ss1[2], pb[[2]], pb[[3]], pc[[2]], pc[[3]], pd[[2]], pd[[3]]}
							]
						] + SolveTrace6[
							Yuk[pd[[1]]], adj[Yuk[pc[[1]]]], Yuk[pb[[1]]], adj[Yuk[ss1[0]]], Yuk[pa[[1]]], adj[Yuk[ss1[0]]],
							Prepend[
								Function[{x}, {pd[[3+x]], pc[[3+x]], pb[[3+x]], ss1[2+x], pa[[3+x]], ss1[2+x]}]/@Range[NumberOfSubgroups],
								{pd[[2]], pd[[3]], pc[[2]], pc[[3]], pb[[2]], pb[[3]], ss1[1], ss1[2], pa[[2]], pa[[3]], ss1[1], ss1[2]}
							]
						]
					],
					{ss1[0], 1, Length[RealScalarList]}
				];
				$Assumptions=assHold;
				sum
			],
			H3[pa_, pb_, pc_, pd_] :> Block[
				{ss1, sum, assHold, x},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
									{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]}
								},
								Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
							]
						],
						SolveTrace6[
							Yuk[pa[[1]]], adj[Yuk[pb[[1]]]], Yuk[ss1[0]], adj[Yuk[pc[[1]]]], Yuk[pd[[1]]], adj[Yuk[ss1[0]]],
							Prepend[
								Function[{x}, {pa[[3+x]], pb[[3+x]], ss1[2+x], pc[[3+x]], pd[[3+x]], ss1[2+x]}]/@Range[NumberOfSubgroups],
								{pa[[2]], pa[[3]], pb[[2]], pb[[3]], ss1[1], ss1[2], pc[[2]], pc[[3]], pd[[2]], pd[[3]], ss1[1], ss1[2]}
							]
						]
					],
					{ss1[0], 1, Length[RealScalarList]}
				];
				$Assumptions=assHold;
				sum
			],
			\[CapitalLambda]bar2S[pa_, pb_, pc_, pd_] :> Block[
				{ss1, ss2, sum, assHold, x},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[contr, ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
								{ss2[1], 1, RealScalarList[[ss2[0], 2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]},
								{ss2[2], 1, RealScalarList[[ss2[0], 2,2]]}
							},
							Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
						]],
						SolveSProd2[
							Quartic[pa[[1]], pb[[1]], ss1[0], ss2[0]],
							Quartic[pc[[1]], pd[[1]], ss1[0], ss2[0]],
							Prepend[
								Function[{x}, {pa[[3+x]], pb[[3+x]], ss1[2+x], ss2[2+x], pc[[3+x]], pd[[3+x]], ss1[2+x], ss2[2+x]}]/@Range[NumberOfSubgroups],
								{pa[[2]], pa[[3]], pb[[2]], pb[[3]], ss1[1], ss1[2], ss2[1], ss2[2], pc[[2]], pc[[3]], pd[[2]], pd[[3]], ss1[1], ss1[2], ss2[1], ss2[2]}
							]
						] Sum[Sqr[ListGauge[[gaug,1]]] C2[RealScalarList[[ss2[0],1]], ListGauge[[gaug,1]]], {gaug, 1, NumberOfSubgroups}]
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]}
				];
				$Assumptions = assHold;
				sum
			],
			\[CapitalLambda]2g[gaug_][pa_, pb_, pc_, pd_] :> Block[
				{ss1, ss2, ss3, ss4, sum, assHold, x},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)&&Element[ss3[x],Integers]&&(ss3[x]>0)&&Element[ss4[x],Integers]&&(ss4[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[contr, ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
								{ss2[1], 1, RealScalarList[[ss2[0], 2,1]]},
								{ss3[1], 1, RealScalarList[[ss3[0], 2,1]]},
								{ss4[1], 1, RealScalarList[[ss4[0], 2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]},
								{ss2[2], 1, RealScalarList[[ss2[0], 2,2]]},
								{ss3[2], 1, RealScalarList[[ss3[0], 2,2]]},
								{ss4[2], 1, RealScalarList[[ss4[0], 2,2]]}
							},
							Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss3[x+2], 1, SMultiplicity[ss3[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss4[x+2], 1, SMultiplicity[ss4[0], x]}]/@Range[NumberOfSubgroups]
						]],
						(
							SolveSProd2[
								Quartic[pa[[1]], pb[[1]], ss1[0], ss2[0]],
								Quartic[pc[[1]], pd[[1]], ss3[0], ss4[0]],
								Prepend[
									Function[{x}, {pa[[3+x]], pb[[3+x]], ss1[2+x], ss2[2+x], pc[[3+x]], pd[[3+x]], ss3[2+x], ss4[2+x]}]/@Range[NumberOfSubgroups],
									{pa[[2]], pa[[3]], pb[[2]], pb[[3]], ss1[1], ss1[2], ss2[1], ss2[2], pc[[2]], pc[[3]], pd[[2]], pd[[3]], ss3[1], ss3[2], ss4[1], ss4[2]}
								]
							]
						)
						\[CapitalLambda][gaug][ss1/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]]//.sub\[CapitalLambda]S
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]},
					{ss3[0], 1, Length[RealScalarList]},
					{ss4[0], 1, Length[RealScalarList]}
				];
				$Assumptions = assHold;
				sum
			],
			HF[pa_, pb_, pc_, pd_] :>Block[
				{ff, x, ii},
				Sum[
					(
						SolveTrace5[
							Delt[ff], Yuk[pa[[1]]], adj[Yuk[pb[[1]]]], Yuk[pc[[1]]], adj[Yuk[pd[[1]]]],
							Prepend[
								Function[{x}, {1, pa[[3+x]], pb[[3+x]], pc[[3+x]], pd[[3+x]]}]/@Range[NumberOfSubgroups],
								{1, 1, pa[[2]], pa[[3]], pb[[2]], pb[[3]], pc[[2]], pc[[3]], pd[[2]], pd[[3]]}
							]
						] +
						SolveTrace5[
							Yuk[pa[[1]]], Delt[ff], adj[Yuk[pb[[1]]]], Yuk[pc[[1]]], adj[Yuk[pd[[1]]]],
							Prepend[
								Function[{x}, {pa[[3+x]], 1, pb[[3+x]], pc[[3+x]], pd[[3+x]]}]/@Range[NumberOfSubgroups],
								{pa[[2]], pa[[3]], 1, 1, pb[[2]], pb[[3]], pc[[2]], pc[[3]], pd[[2]], pd[[3]]}
							]
						]
					) Sum[Sqr[ListGauge[[ii,1]]] C2[WeylFermionList[[ff,1]], ListGauge[[ii,1]]], {ii, 1, NumberOfSubgroups}],
					{ff, 1, Length[WeylFermionList]}
				]
			]/.{tr[A___,C2[B___], C___]:>C2[B] tr[A,C]},
			A\[Lambda][gauge_, gauge2_][a_, b_, c_, d_] :> Block[
				{ss1, ss2, ss3, ss4, sum, assHold},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)&&Element[ss3[x],Integers]&&(ss3[x]>0)&&Element[ss4[x],Integers]&&(ss4[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
									{ss2[1], 1, RealScalarList[[ss2[0], 2,1]]},
									{ss3[1], 1, RealScalarList[[ss3[0], 2,1]]},
									{ss4[1], 1, RealScalarList[[ss4[0], 2,1]]},
									{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]},
									{ss2[2], 1, RealScalarList[[ss2[0], 2,2]]},
									{ss3[2], 1, RealScalarList[[ss3[0], 2,2]]},
									{ss4[2], 1, RealScalarList[[ss4[0], 2,2]]}
								},
								Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss3[x+2], 1, SMultiplicity[ss3[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss4[x+2], 1, SMultiplicity[ss4[0], x]}]/@Range[NumberOfSubgroups]
							]
						], 
						BetaQuartic[a[[1]], b[[1]], ss1[0], ss2[0], a[[2;;]], b[[2;;]], ss1/@Range[NumberOfSubgroups+2], ss2/@Range[NumberOfSubgroups+2], 0](
							\[CapitalLambda][gauge][ss1/@Range[0,NumberOfSubgroups+2], c, ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge2][ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2], d] +
							\[CapitalLambda][gauge][ss1/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], d] \[CapitalLambda][gauge2][ss3/@Range[0,NumberOfSubgroups+2], c, ss2/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] +
							\[CapitalLambda][gauge][ss3/@Range[0,NumberOfSubgroups+2], c, ss2/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge2][ss1/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], d] +
							\[CapitalLambda][gauge][ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2], d] \[CapitalLambda][gauge2][ss1/@Range[0,NumberOfSubgroups+2], c, ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]]
						)//.sub\[CapitalLambda]S
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]},
					{ss3[0], 1, Length[RealScalarList]},
					{ss4[0], 1, Length[RealScalarList]}
				];
				$Assumptions=assHold;
				sum
			],
			Abar\[Lambda][gauge_, gauge2_][a_, b_, c_, d_] :> Block[
				{ss1, ss2, ss3, ss4, sum, assHold},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)&&Element[ss3[x],Integers]&&(ss3[x]>0)&&Element[ss4[x],Integers]&&(ss4[x]>0)]/@Range[NumberOfSubgroups+2];
				sum = Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
									{ss2[1], 1, RealScalarList[[ss2[0], 2,1]]},
									{ss3[1], 1, RealScalarList[[ss3[0], 2,1]]},
									{ss4[1], 1, RealScalarList[[ss4[0], 2,1]]},
									{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]},
									{ss2[2], 1, RealScalarList[[ss2[0], 2,2]]},
									{ss3[2], 1, RealScalarList[[ss3[0], 2,2]]},
									{ss4[2], 1, RealScalarList[[ss4[0], 2,2]]}
								},
								Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss3[x+2], 1, SMultiplicity[ss3[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss4[x+2], 1, SMultiplicity[ss4[0], x]}]/@Range[NumberOfSubgroups]
							]
						],
						BetaQuartic[a[[1]], b[[1]], ss1[0], ss2[0], a[[2;;]], b[[2;;]], ss1/@Range[NumberOfSubgroups+2], ss2/@Range[NumberOfSubgroups+2], 0](
							\[CapitalLambda][gauge][c, d, ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge2][ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss1/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2]] +
							\[CapitalLambda][gauge][c, ss4/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge2][ss3/@Range[0,NumberOfSubgroups+2], d, ss1/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] +
							\[CapitalLambda][gauge][ss3/@Range[0,NumberOfSubgroups+2], d, ss1/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge2][c, ss4/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2]] +
							\[CapitalLambda][gauge][ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss1/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge2][c, d, ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]]
						)//.sub\[CapitalLambda]S
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]},
					{ss3[0], 1, Length[RealScalarList]},
					{ss4[0], 1, Length[RealScalarList]}
				];
				$Assumptions=assHold;
				sum
			],
			BY[gauge_, gauge2_][a_, b_, c_, d_] :> Block[
				{gg, ff, ff1, ff2, ff3, ff4, y2, y3},
				Sum[
					(ReleaseHold[tr[Yuk[c[[1]]][AdjWeylFermionList[[ff1[0],3]], ff4[0]], adj[Yuk[d[[1]]]][AdjWeylFermionList[[ff4[0],3]], ff1[0]]]//. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk1 //.subProd]//.subYuk2 /.{
						tr[y2_, y3_]:>(
							Sum[
								ApplyDistribute[
									Function[contr,
										ContractSum@@Join[
											{
												contr,
												{gg[1], 1, RealScalarList[[gg[0], 2, 1]]},
												{gg[2], 1, RealScalarList[[gg[0], 2, 2]]}
											},
											Function[{x}, {gg[x+2], 1, SMultiplicity[gg[0],x]}]/@Range[NumberOfSubgroups],
											Function[{x}, {ff1[x], 1, FMultiplicity[AdjWeylFermionList[[ff1[0], 2]],x]}]/@Range[NumberOfSubgroups],
											Function[{x}, {ff2[x], 1, FMultiplicity[AdjWeylFermionList[[ff1[0], 2]],x]}]/@Range[NumberOfSubgroups],
											Function[{x}, {ff3[x], 1, FMultiplicity[AdjWeylFermionList[[ff1[0], 2]],x]}]/@Range[NumberOfSubgroups],
											Function[{x}, {ff4[x], 1, FMultiplicity[AdjWeylFermionList[[ff4[0], 2]],x]}]/@Range[NumberOfSubgroups]
										]
									],
									GetGenTrace[{y2, y3}, {{c[[2]], c[[3]]}, {d[[2]], d[[3]]}}] Times@@(Function[{x2}, y2[[1+x2,1]][c[[3+x2]], ff3[x2], ff4[x2]] y3[[1+x2,1]][d[[3+x2]], ff4[x2], ff1[x2]]]/@Range[NumberOfSubgroups]) Refine[(
										\[CapitalLambda][gauge][a, Join[{ff1[0], 1}, ff2/@Range[NumberOfSubgroups]], gg/@Range[0,NumberOfSubgroups+2], Join[{AdjWeylFermionList[[ff1[0],3]], 1}, ff1/@Range[NumberOfSubgroups]]] \[CapitalLambda][gauge2][gg/@Range[0,NumberOfSubgroups+2], Join[{ff1[0], 1}, ff3/@Range[NumberOfSubgroups]], b, Join[{AdjWeylFermionList[[ff1[0],3]], 1}, ff2/@Range[NumberOfSubgroups]]] +
										\[CapitalLambda][gauge2][a, Join[{ff1[0], 1}, ff3/@Range[NumberOfSubgroups]], gg/@Range[0,NumberOfSubgroups+2], Join[{AdjWeylFermionList[[ff1[0],3]], 1}, ff2/@Range[NumberOfSubgroups]]] \[CapitalLambda][gauge][gg/@Range[0,NumberOfSubgroups+2], Join[{ff1[0], 1}, ff2/@Range[NumberOfSubgroups]], b, Join[{AdjWeylFermionList[[ff1[0],3]], 1}, ff1/@Range[NumberOfSubgroups]]]
									)//.sub\[CapitalLambda]SF]
								],
								{gg[0], 1, Length[RealScalarList]}
							]
						)
					}) +
					(ReleaseHold[tr[adj[Yuk[d[[1]]]][AdjWeylFermionList[[ff1[0],3]], ff4[0]], Yuk[c[[1]]][AdjWeylFermionList[[ff4[0],3]], ff1[0]]]//. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk1 //.subProd]//.subYuk2 /.{
						tr[y2_, y3_]:>(
							Sum[
								ApplyDistribute[
									Function[contr,
										ContractSum@@Join[
											{
												contr,
												{gg[1], 1, RealScalarList[[gg[0], 2, 1]]},
												{gg[2], 1, RealScalarList[[gg[0], 2, 2]]}
											},
											Function[{x}, {gg[x+2], 1, SMultiplicity[gg[0], x]}]/@Range[NumberOfSubgroups],
											Function[{x}, {ff1[x], 1, FMultiplicity[AdjWeylFermionList[[ff1[0], 2]],x]}]/@Range[NumberOfSubgroups],
											Function[{x}, {ff2[x], 1, FMultiplicity[AdjWeylFermionList[[ff1[0], 2]],x]}]/@Range[NumberOfSubgroups],
											Function[{x}, {ff3[x], 1, FMultiplicity[AdjWeylFermionList[[ff1[0], 2]],x]}]/@Range[NumberOfSubgroups],
											Function[{x}, {ff4[x], 1, FMultiplicity[AdjWeylFermionList[[ff4[0], 2]],x]}]/@Range[NumberOfSubgroups]
										]
									],
									GetGenTrace[{y2, y3}, {{d[[2]], d[[3]]}, {c[[2]], c[[3]]}}]*Times@@(Function[{x2}, y2[[1+x2,1]][d[[3+x2]], ff3[x2], ff4[x2]] y3[[1+x2,1]][c[[3+x2]], ff4[x2], ff1[x2]]]/@Range[NumberOfSubgroups]) Refine[(
										\[CapitalLambda][gauge][a, Join[{AdjWeylFermionList[[ff1[0],3]], 1}, ff1/@Range[NumberOfSubgroups]], gg/@Range[0,NumberOfSubgroups+2], Join[{ff1[0], 1}, ff2/@Range[NumberOfSubgroups]]] \[CapitalLambda][gauge2][gg/@Range[0,NumberOfSubgroups+2], Join[{AdjWeylFermionList[[ff1[0],3]], 1}, ff2/@Range[NumberOfSubgroups]], b, Join[{ff1[0], 1}, ff3/@Range[NumberOfSubgroups]]] +
										\[CapitalLambda][gauge2][a, Join[{AdjWeylFermionList[[ff1[0],3]], 1}, ff2/@Range[NumberOfSubgroups]], gg/@Range[0,NumberOfSubgroups+2], Join[{ff1[0], 1}, ff3/@Range[NumberOfSubgroups]]] \[CapitalLambda][gauge][gg/@Range[0,NumberOfSubgroups+2], Join[{AdjWeylFermionList[[ff1[0],3]], 1}, ff1/@Range[NumberOfSubgroups]], b, Join[{ff1[0], 1}, ff2/@Range[NumberOfSubgroups]]]
									)//.sub\[CapitalLambda]SF]
								],
								{gg[0], 1, Length[RealScalarList]}
							]
						)
					}),
					{ff1[0], 1, Length[AdjWeylFermionList]},
					{ff4[0], 1, Length[AdjWeylFermionList]}
				]
			],
			BbarY[gauge_, gauge2_][a_, b_, c_, d_] :> Block[
				{ffA, ffB, gg, y2, y4},
				Sum[
					ReleaseHold[tr[Yuk[c[[1]]][AdjWeylFermionList[[ff1[0],3]], ff3[0]], adj[Yuk[d[[1]]]][AdjWeylFermionList[[ff3[0],3]], ff1[0]]] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk1 //.subProd]//.subYuk2 /.{
						tr[y2_, y4_] :> (
							Sum[
								ApplyDistribute[
									Function[contr,
										ContractSum@@Join[
											{
												contr,
												{gg[1], 1, RealScalarList[[gg[0], 2, 1]]},
												{gg[2], 1, RealScalarList[[gg[0], 2, 2]]}
											},
											Function[{x}, {gg[x+2], 1, SMultiplicity[gg[0], x]}]/@Range[NumberOfSubgroups],
											Function[{x}, {ff1[x], 1, FMultiplicity[AdjWeylFermionList[[ff1[0], 2]],x]}]/@Range[NumberOfSubgroups],
											Function[{x}, {ff2[x], 1, FMultiplicity[AdjWeylFermionList[[ff1[0], 2]],x]}]/@Range[NumberOfSubgroups],
											Function[{x}, {ff3[x], 1, FMultiplicity[AdjWeylFermionList[[ff3[0], 2]],x]}]/@Range[NumberOfSubgroups],
											Function[{x}, {ff4[x], 1, FMultiplicity[AdjWeylFermionList[[ff3[0], 2]],x]}]/@Range[NumberOfSubgroups]
										]
									],
									GetGenTrace[{ y2, y4}, {{c[[2]], c[[3]]}, {d[[2]], d[[3]]}}]*Times@@(Function[{x2}, y2[[1+x2,1]][c[[3+x2]], ff2[x2], ff3[x2]] y4[[1+x2,1]][d[[3+x2]], ff4[x2], ff1[x2]]]/@Range[NumberOfSubgroups]) Refine[(
										\[CapitalLambda][gauge][a, Join[{ff1[0], 1}, ff2/@Range[NumberOfSubgroups]], gg/@Range[0,NumberOfSubgroups+2], Join[{AdjWeylFermionList[[ff1[0],3]], 1}, ff1/@Range[NumberOfSubgroups]]] \[CapitalLambda][gauge2][gg/@Range[0,NumberOfSubgroups+2], Join[{AdjWeylFermionList[[ff3[0],3]], 1}, ff3/@Range[NumberOfSubgroups]], b, Join[{ff3[0], 1}, ff4/@Range[NumberOfSubgroups]]] +
										\[CapitalLambda][gauge2][a, Join[{AdjWeylFermionList[[ff3[0],3]], 1}, ff3/@Range[NumberOfSubgroups]], gg/@Range[0,NumberOfSubgroups+2], Join[{ff3[0], 1}, ff4/@Range[NumberOfSubgroups]]] \[CapitalLambda][gauge][gg/@Range[0,NumberOfSubgroups+2], Join[{ff1[0], 1}, ff2/@Range[NumberOfSubgroups]], b, Join[{AdjWeylFermionList[[ff1[0],3]], 1}, ff1/@Range[NumberOfSubgroups]]]
									)//.sub\[CapitalLambda]SF]
								],
								{gg[0], 1, Length[RealScalarList]}
							]
						)
					},
					{ff1[0], 1, Length[AdjWeylFermionList]},
					{ff3[0], 1, Length[AdjWeylFermionList]}
				]
			],
			Ag[gauge_][a_, b_, c_, d_] :> Block[
				{ss1, ss2, ss3, ss4, sum, assHold},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)&&Element[ss3[x],Integers]&&(ss3[x]>0)&&Element[ss4[x],Integers]&&(ss4[x]>0)]/@Range[NumberOfSubgroups+2];
				sum=Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
									{ss2[1], 1, RealScalarList[[ss2[0], 2,1]]},
									{ss3[1], 1, RealScalarList[[ss3[0], 2,1]]},
									{ss4[1], 1, RealScalarList[[ss4[0], 2,1]]},
									{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]},
									{ss2[2], 1, RealScalarList[[ss2[0], 2,2]]},
									{ss3[2], 1, RealScalarList[[ss3[0], 2,2]]},
									{ss4[2], 1, RealScalarList[[ss4[0], 2,2]]}
								},
								Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss3[x+2], 1, SMultiplicity[ss3[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss4[x+2], 1, SMultiplicity[ss4[0], x]}]/@Range[NumberOfSubgroups]
							]
						],
						\[CapitalLambda][gauge][a, c, ss1/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2]] (
							\[CapitalLambda][gauge][ss1/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2], d] \[CapitalLambda][gauge][ss2/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], b, ss4/@Range[0,NumberOfSubgroups+2]] - 3 \[CapitalLambda][gauge][ss1/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge][ss2/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], b, d]
						)//.sub\[CapitalLambda]S
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]},
					{ss3[0], 1, Length[RealScalarList]},
					{ss4[0], 1, Length[RealScalarList]}
				];
				$Assumptions=assHold;
				sum
			],
			\[CapitalLambda]G2[ii_] :> Block[
				{ss1, ss2, ss3, ss4, sum, assHold},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)&&Element[ss3[x],Integers]&&(ss3[x]>0)&&Element[ss4[x],Integers]&&(ss4[x]>0)]/@Range[NumberOfSubgroups+2];
				sum=Sum[
					ApplyDistribute[
						Function[ contr, ContractSum@@Join[
							{
								contr,
								{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
								{ss2[1], 1, RealScalarList[[ss2[0], 2,1]]},
								{ss3[1], 1, RealScalarList[[ss3[0], 2,1]]},
								{ss4[1], 1, RealScalarList[[ss4[0], 2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]},
								{ss2[2], 1, RealScalarList[[ss2[0], 2,2]]},
								{ss3[2], 1, RealScalarList[[ss3[0], 2,2]]},
								{ss4[2], 1, RealScalarList[[ss4[0], 2,2]]}
							},
							Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss3[x+2], 1, SMultiplicity[ss3[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss4[x+2], 1, SMultiplicity[ss4[0], x]}]/@Range[NumberOfSubgroups]
						]],
						Sqr[24]/d[ListGauge[[ii, 1]]] \[Alpha][ListGauge[[ii,1]]]^2 C2[RealScalarList[[ss1[0], 1]], ListGauge[[ii,1]]] SolveSProd2[
							Quartic[ss1[0], ss2[0], ss3[0], ss4[0]],
							Quartic[ss1[0], ss2[0], ss3[0], ss4[0]],
							Prepend[
								Function[{x}, {ss1[2+x], ss2[2+x], ss3[2+x], ss4[2+x], ss1[2+x], ss2[2+x], ss3[2+x], ss4[2+x]}]/@Range[NumberOfSubgroups],
								{ss1[1], ss1[2], ss2[1], ss2[2], ss3[1], ss3[2], ss4[1], ss4[2], ss1[1], ss1[2], ss2[1], ss2[2], ss3[1], ss3[2], ss4[1], ss4[2]}
							]
						]

					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]},
					{ss3[0], 1, Length[RealScalarList]},
					{ss4[0], 1, Length[RealScalarList]}
				];
				$Assumptions=assHold;
				sum
			],
			\[Lambda]\[CapitalLambda]2[ii_, jj_] :> Block[
				{ss1, ss2, ss3, ss4, ss5, ss6, sum, assHold},
				assHold=$Assumptions;
				$Assumptions=$Assumptions&&And@@Function[{x}, Element[ss1[x],Integers]&&(ss1[x]>0)&&Element[ss2[x],Integers]&&(ss2[x]>0)&&Element[ss3[x],Integers]&&(ss3[x]>0)&&Element[ss4[x],Integers]&&(ss4[x]>0)]/@Range[NumberOfSubgroups+2];
				sum=Sum[
					ApplyDistribute[
						Function[contr,
							ContractSum@@Join[
								{
									contr,
									{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
									{ss2[1], 1, RealScalarList[[ss2[0], 2,1]]},
									{ss3[1], 1, RealScalarList[[ss3[0], 2,1]]},
									{ss4[1], 1, RealScalarList[[ss4[0], 2,1]]},
									{ss5[1], 1, RealScalarList[[ss5[0], 2,1]]},
									{ss6[1], 1, RealScalarList[[ss6[0], 2,1]]},
									{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]},
									{ss2[2], 1, RealScalarList[[ss2[0], 2,2]]},
									{ss3[2], 1, RealScalarList[[ss3[0], 2,2]]},
									{ss4[2], 1, RealScalarList[[ss4[0], 2,2]]},
									{ss5[2], 1, RealScalarList[[ss5[0], 2,2]]},
									{ss6[2], 1, RealScalarList[[ss6[0], 2,2]]}
								},
								Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss3[x+2], 1, SMultiplicity[ss3[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss4[x+2], 1, SMultiplicity[ss4[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss5[x+2], 1, SMultiplicity[ss5[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x}, {ss6[x+2], 1, SMultiplicity[ss6[0], x]}]/@Range[NumberOfSubgroups]
							]
						],
						24 BetaQuartic[ss1[0], ss2[0], ss3[0], ss4[0], ss1/@Range[NumberOfSubgroups+2], ss2/@Range[NumberOfSubgroups+2], ss3/@Range[NumberOfSubgroups+2], ss4/@Range[NumberOfSubgroups+2], 0] (
							\[CapitalLambda][ii][ss1/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], ss5/@Range[0,NumberOfSubgroups+2], ss6/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][jj][ss5/@Range[0,NumberOfSubgroups+2], ss6/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]]/2 + \[CapitalLambda][jj][ss1/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], ss5/@Range[0,NumberOfSubgroups+2], ss6/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][ii][ss5/@Range[0,NumberOfSubgroups+2], ss6/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]]/2 //. sub\[CapitalLambda]S)
					],
					{ss1[0], 1, Length[RealScalarList]},
					{ss2[0], 1, Length[RealScalarList]},
					{ss3[0], 1, Length[RealScalarList]},
					{ss4[0], 1, Length[RealScalarList]},
					{ss5[0], 1, Length[RealScalarList]},
					{ss6[0], 1, Length[RealScalarList]}
				];
				$Assumptions=assHold;
				sum
			]
		}];

		(* trivial thing the kernel should be aware of but isn't *)
		subKron := {Sum[AA_ KroneckerDelta[aa_, 1], BB___, {aa_, 1, bb_}, CC__] :> Sum[AA /. aa -> 1, BB, CC]};

		(* Contraction of two scalar generators, see for instance arXiv:hep-ph/0211440 eq. (117) for Scalars and Fermions*)
		sub\[CapitalLambda]S := Dispatch[{
			(** At least one is a dummy field *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;(a[[1]] > Length[RealScalarList] || b[[1]] > Length[RealScalarList] || c[[1]] > Length[RealScalarList] || d[[1]] > Length[RealScalarList]),
			(** Different Scalar Fields *)
			\[CapitalLambda][_][a_, b_, c_, d_] :> (0)/;(
				(Length[RealScalarList[[a[[1]],1]]] =!= Length[RealScalarList[[c[[1]],1]]]) ||
				(Length[RealScalarList[[a[[1]],1]]] === 0 && a[[1]] != c[[1]]) ||
				(Length[RealScalarList[[a[[1]],1]]] === 1 && RealScalarList[[a[[1]],1]][[1]] != RealScalarList[[c[[1]],1]][[1]])
			),
			\[CapitalLambda][_][a_, b_, c_, d_] :> (0)/;(
				(Length[RealScalarList[[b[[1]],1]]] =!= Length[RealScalarList[[d[[1]],1]]]) ||
				(Length[RealScalarList[[b[[1]],1]]] === 0 && b[[1]] != d[[1]]) ||
				(Length[RealScalarList[[b[[1]],1]]] === 1 && RealScalarList[[b[[1]],1]][[1]] != RealScalarList[[d[[1]],1]][[1]])
			),
			(** At least one is gauge singlet *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;(ListGauge[[gaug,3]] =!= 1 && (RealScalarList[[a[[1]],3,gaug]] == 1 || RealScalarList[[b[[1]],3,gaug]] == 1 || RealScalarList[[c[[1]],3,gaug]] == 1 || RealScalarList[[d[[1]],3,gaug]] == 1)),
			(** Gauge Multiplicities do not match *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;(RealScalarList[[a[[1]],3,gaug]] =!= RealScalarList[[c[[1]],3,gaug]] || RealScalarList[[b[[1]],3,gaug]] =!= RealScalarList[[d[[1]],3,gaug]]),
			(** SU(N) -- all in fundamental representation *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (
				If[
					(a[[1]] == c[[1]] && b[[1]] == d[[1]])
					,
					1/4(KroneckerDelta[a[[gaug+3]],d[[gaug+3]]] KroneckerDelta[b[[gaug+3]],c[[gaug+3]]]  - KroneckerDelta[a[[gaug+3]],b[[gaug+3]]] KroneckerDelta[c[[gaug+3]],d[[gaug+3]]]) TensorDelta[Delete[a,gaug+3][[2;;]], Delete[c,gaug+3][[2;;]]] TensorDelta[Delete[b,gaug+3][[2;;]], Delete[d,gaug+3][[2;;]]]
					,
					0
				] + If[
						(RealScalarList[[a[[1]], 1]][[1]] === RealScalarList[[c[[1]], 1]][[1]] &&  RealScalarList[[b[[1]], 1]][[1]] === RealScalarList[[d[[1]], 1]][[1]] &&
						RealScalarList[[a[[1]], 1]][[0]] =!= RealScalarList[[c[[1]], 1]][[0]] &&  RealScalarList[[b[[1]], 1]][[0]] =!= RealScalarList[[d[[1]], 1]][[0]] &&
						RealScalarList[[a[[1]], 1]][[0]] === RealScalarList[[b[[1]], 1]][[0]] && RealScalarList[[c[[1]], 1]][[0]] === RealScalarList[[d[[1]], 1]][[0]]),
						-1/4(KroneckerDelta[a[[gaug+3]],d[[gaug+3]]] KroneckerDelta[b[[gaug+3]],c[[gaug+3]]] + KroneckerDelta[a[[gaug+3]],b[[gaug+3]]] KroneckerDelta[c[[gaug+3]],d[[gaug+3]]] - 2/ListGauge[[gaug,3]] KroneckerDelta[a[[gaug+3]],c[[gaug+3]]] KroneckerDelta[b[[gaug+3]],d[[gaug+3]]]) TensorDelta[Delete[a,gaug+3][[2;;]], Delete[c,gaug+3][[2;;]]] TensorDelta[Delete[b,gaug+3][[2;;]], Delete[d,gaug+3][[2;;]]]
						 ,
						0
					] + If[
							(RealScalarList[[a[[1]], 1]][[1]] === RealScalarList[[c[[1]], 1]][[1]] &&  RealScalarList[[b[[1]], 1]][[1]] === RealScalarList[[d[[1]], 1]][[1]] &&
							RealScalarList[[a[[1]], 1]][[0]] =!= RealScalarList[[c[[1]], 1]][[0]] &&  RealScalarList[[b[[1]], 1]][[0]] =!= RealScalarList[[d[[1]], 1]][[0]] &&
							RealScalarList[[a[[1]], 1]][[0]] === RealScalarList[[d[[1]], 1]][[0]] && RealScalarList[[b[[1]], 1]][[0]] === RealScalarList[[c[[1]], 1]][[0]]),
							+1/4(KroneckerDelta[a[[gaug+3]],d[[gaug+3]]] KroneckerDelta[b[[gaug+3]],c[[gaug+3]]] + KroneckerDelta[a[[gaug+3]],b[[gaug+3]]] KroneckerDelta[c[[gaug+3]],d[[gaug+3]]] - 2/ListGauge[[gaug,3]] KroneckerDelta[a[[gaug+3]],c[[gaug+3]]] KroneckerDelta[b[[gaug+3]],d[[gaug+3]]]) TensorDelta[Delete[a,gaug+3][[2;;]], Delete[c,gaug+3][[2;;]]] TensorDelta[Delete[b,gaug+3][[2;;]], Delete[d,gaug+3][[2;;]]]
							,
							0
						]
			)/;(
				ListGauge[[gaug,2]] === SU &&
				RealScalarList[[a[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				RealScalarList[[b[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				RealScalarList[[c[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				RealScalarList[[d[[1]], 3, gaug]] == ListGauge[[gaug,3]]
			),
			(** SO(N) -- all in fundamental representation *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (
				1/4 (KroneckerDelta[a[[gaug+3]],d[[gaug+3]]] KroneckerDelta[b[[gaug+3]],c[[gaug+3]]] - KroneckerDelta[a[[gaug+3]],b[[gaug+3]]] KroneckerDelta[c[[gaug+3]],d[[gaug+3]]]) TensorDelta[Delete[a,gaug+3], Delete[c,gaug+3]] TensorDelta[Delete[b,gaug+3], Delete[d,gaug+3]]
			)/;(
				ListGauge[[gaug,2]] === SO &&
				RealScalarList[[a[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				RealScalarList[[b[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				RealScalarList[[c[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				RealScalarList[[d[[1]], 3, gaug]] == ListGauge[[gaug,3]]
			),
			(** U(1) *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :>(
				(
					RealScalarList[[a[[1]],3,gaug]] RealScalarList[[b[[1]],3,gaug]]
					ComplexDelta[RealScalarList[[a[[1]],1]], RealScalarList[[c[[1]],1]]] ComplexDelta[RealScalarList[[b[[1]],1]], RealScalarList[[d[[1]],1]]]
					(If[RealScalarList[[a[[1]],1]][[0]] === RealScalarList[[c[[1]],1]][[0]] || RealScalarList[[b[[1]],1]][[0]] === RealScalarList[[d[[1]],1]][[0]], 0,
						If[RealScalarList[[a[[1]],1]][[0]] === RealScalarList[[b[[1]],1]][[0]], -1, 1]
					])
					TensorDelta[a[[2;;]],c[[2;;]]] TensorDelta[b[[2;;]],d[[2;;]]]
				)
			)/;(ListGauge[[gaug, 3]] === 1),
			(** unknown gauge group*)
			\[CapitalLambda][gaug_][a_,b_, c_, d_] :>(\[CapitalLambda][ListGauge[[gaug,1]], RealScalarList[[a[[1]],1]], RealScalarList[[b[[1]],1]], RealScalarList[[c[[1]],1]], RealScalarList[[d[[1]],1]]][a[[3+gaug]], b[[3+gaug]], c[[3+gaug]], d[[3+gaug]]] TensorDelta[a[[2;;2+gaug]], c[[2;;2+gaug]]] TensorDelta[b[[2;;2+gaug]], d[[2;;2+gaug]]] TensorDelta[a[[4+gaug;;]], c[[4+gaug;;]]] TensorDelta[b[[4+gaug;;]], d[[4+gaug;;]]])
		}];

		sub\[CapitalLambda]F := Dispatch[{
			(** Generator between different particle types *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;(
				(AdjWeylFermionList[[a[[1]],2]] != AdjWeylFermionList[[c[[1]],2]]) || (AdjWeylFermionList[[b[[1]],2]] != AdjWeylFermionList[[d[[1]],2]])
			),
			(** At least one is gauge singlet *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;(
				ListGauge[[gaug,3]] =!= 1 && (WeylFermionList[[AdjWeylFermionList[[a[[1]],2]],3,gaug]] == 1 || WeylFermionList[[AdjWeylFermionList[[b[[1]],2]],3,gaug]] == 1 || WeylFermionList[[AdjWeylFermionList[[c[[1]],2]],3,gaug]] == 1 || WeylFermionList[[AdjWeylFermionList[[d[[1]],2]],3,gaug]] == 1)
			),
			(** Gauge Multiplicities do not match *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;((WeylFermionList[[AdjWeylFermionList[[a[[1]],2]],3,gaug]] =!= WeylFermionList[[AdjWeylFermionList[[c[[1]],2]],3,gaug]]) || (WeylFermionList[[AdjWeylFermionList[[b[[1]],2]],3,gaug]] =!= WeylFermionList[[AdjWeylFermionList[[d[[1]],2]],3,gaug]])
			),
			(** SU(N) -- all in fundamental representation *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (\[CapitalLambda][gaug][c, b, a, d])/;(
				ListGauge[[gaug,2]] === SU &&
				WeylFermionList[[AdjWeylFermionList[[a[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[c[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[d[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				a[[1]] == AdjWeylFermionList[[a[[1]], 4]] && AdjWeylFermionList[[c[[1]], 3]] == a[[1]]
			),
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (\[CapitalLambda][gaug][a, d, c, b])/;(
				ListGauge[[gaug,2]] === SU &&
				WeylFermionList[[AdjWeylFermionList[[a[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[c[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[d[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				b[[1]] == AdjWeylFermionList[[b[[1]], 4]] && AdjWeylFermionList[[d[[1]], 3]] == b[[1]]
			),
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (
				1/2(KroneckerDelta[a[[gaug+2]],d[[gaug+2]]] KroneckerDelta[b[[gaug+2]],c[[gaug+2]]]  - 1/ListGauge[[gaug,3]] KroneckerDelta[a[[gaug+2]],c[[gaug+2]]] KroneckerDelta[b[[gaug+2]],d[[gaug+2]]]) TensorDelta[Delete[a,gaug+2][[2;;]], Delete[c,gaug+2][[2;;]]] TensorDelta[Delete[b,gaug+2][[2;;]], Delete[d,gaug+2][[2;;]]] KroneckerDelta[AdjWeylFermionList[[a[[1]],3]], c[[1]]] KroneckerDelta[AdjWeylFermionList[[c[[1]],4]], c[[1]]] KroneckerDelta[AdjWeylFermionList[[b[[1]],3]], d[[1]]] KroneckerDelta[AdjWeylFermionList[[d[[1]],4]], d[[1]]]
			)/;(
				ListGauge[[gaug,2]] === SU &&
				WeylFermionList[[AdjWeylFermionList[[a[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[c[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[d[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]]
			),
			(** SO(N) -- all in fundamental representation *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (\[CapitalLambda][gaug][c, b, a, d])/;(
				ListGauge[[gaug,2]] === SO &&
				WeylFermionList[[AdjWeylFermionList[[a[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[c[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[d[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				a[[1]] == AdjWeylFermionList[[a[[1]], 4]] && AdjWeylFermionList[[c[[1]], 3]] == a[[1]]
			),
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (\[CapitalLambda][gaug][a, d, c, b])/;(
				ListGauge[[gaug,2]] === SO &&
				WeylFermionList[[AdjWeylFermionList[[a[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[c[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[d[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				b[[1]] == AdjWeylFermionList[[b[[1]], 4]] && AdjWeylFermionList[[d[[1]], 3]] == b[[1]]
			),
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (
				1/4 (KroneckerDelta[a[[gaug+2]],d[[gaug+2]]] KroneckerDelta[b[[gaug+2]],c[[gaug+2]]] - KroneckerDelta[a[[gaug+2]],b[[gaug+2]]] KroneckerDelta[c[[gaug+2]],d[[gaug+2]]]) TensorDelta[Delete[a,gaug+2][[2;;]], Delete[c,gaug+2][[2;;]]] TensorDelta[Delete[b,gaug+2][[2;;]], Delete[d,gaug+2][[2;;]]] KroneckerDelta[AdjWeylFermionList[[a[[1]],3]], c[[1]]] KroneckerDelta[AdjWeylFermionList[[c[[1]],4]], c[[1]]] KroneckerDelta[AdjWeylFermionList[[b[[1]],3]], d[[1]]] KroneckerDelta[AdjWeylFermionList[[d[[1]],4]], d[[1]]]
			)/;(
				ListGauge[[gaug,2]] === SO &&
				WeylFermionList[[AdjWeylFermionList[[a[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[c[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[d[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]]
			),
			(** U(1) *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :>(
					WeylFermionList[[AdjWeylFermionList[[a[[1]], 2]], 3, gaug]] WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] TensorDelta[a[[2;;]],c[[2;;]]] TensorDelta[b[[2;;]],d[[2;;]]] KroneckerDelta[AdjWeylFermionList[[a[[1]],3]], c[[1]]] KroneckerDelta[AdjWeylFermionList[[c[[1]],3]], a[[1]]] KroneckerDelta[AdjWeylFermionList[[b[[1]],3]], d[[1]]] KroneckerDelta[AdjWeylFermionList[[d[[1]],3]], b[[1]]]
			)/;(ListGauge[[gaug, 3]] === 1),
			(** unknown gauge group*)
			\[CapitalLambda][gaug_][a_,b_, c_, d_] :>(\[CapitalLambda][ListGauge[[gaug,1]], AdjWeylFermionList[[a[[1]],1]], AdjWeylFermionList[[b[[1]],1]], AdjWeylFermionList[[c[[1]],1]], AdjWeylFermionList[[d[[1]],1]]][a[[2+gaug]], b[[2+gaug]], c[[2+gaug]], d[[2+gaug]]] TensorDelta[a[[2;;1+gaug]], c[[2;;1+gaug]]] TensorDelta[b[[2;;1+gaug]], d[[2;;1+gaug]]] TensorDelta[a[[3+gaug;;]], c[[3+gaug;;]]] TensorDelta[b[[3+gaug;;]], d[[3+gaug;;]]])
		}];

		sub\[CapitalLambda]SF := Dispatch[{
			(** At least one is a dummy field *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;(a[[1]] > Length[RealScalarList] || c[[1]] > Length[RealScalarList]),
			(** Fermion Fields are different Weyl Fermions *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;(AdjWeylFermionList[[b[[1]], 2]] != AdjWeylFermionList[[d[[1]], 2]]),
			(** Scalar Fields are different *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;(
				(Length[RealScalarList[[a[[1]],1]]] =!= Length[RealScalarList[[c[[1]],1]]]) ||
				(Length[RealScalarList[[a[[1]],1]]] === 0 && a[[1]] != c[[1]]) ||
				(Length[RealScalarList[[a[[1]],1]]] === 1 && RealScalarList[[a[[1]],1]][[1]] != RealScalarList[[c[[1]],1]][[1]])
			),
			(** At least one is gauge singlet *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;(ListGauge[[gaug,3]] =!= 1 && (RealScalarList[[a[[1]],3,gaug]] == 1 || WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] == 1 || RealScalarList[[c[[1]],3,gaug]] == 1 || WeylFermionList[[AdjWeylFermionList[[d[[1]], 2]], 3, gaug]] == 1)),
			(** Gauge Multiplicities do not match *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;((RealScalarList[[a[[1]],3,gaug]] =!= RealScalarList[[c[[1]],3,gaug]]) || (WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] =!= WeylFermionList[[AdjWeylFermionList[[d[[1]], 2]], 3, gaug]])),
			(** SU(N) -- all in fundamental representation *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> ( \[CapitalLambda][gaug][a, d, c, b] ) /;(
				ListGauge[[gaug,2]] === SU &&
				RealScalarList[[a[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				RealScalarList[[c[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[d[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				AdjWeylFermionList[[b[[1]], 4]] == b[[1]] && AdjWeylFermionList[[b[[1]], 3]] == d[[1]]
			),
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (
				If[
					(a[[1]] == c[[1]])
					,
					1/4 (KroneckerDelta[a[[gaug+3]],d[[gaug+2]]] KroneckerDelta[b[[gaug+2]],c[[gaug+3]]]  - KroneckerDelta[a[[gaug+3]],b[[gaug+2]]] KroneckerDelta[c[[gaug+3]],d[[gaug+2]]])
					,
					0
				] + If[
						(RealScalarList[[a[[1]], 1]][[1]] === RealScalarList[[c[[1]], 1]][[1]] &&
						RealScalarList[[a[[1]], 1]][[0]] =!= RealScalarList[[c[[1]], 1]][[0]] &&
						RealScalarList[[a[[1]], 1]][[0]] === Re && RealScalarList[[c[[1]], 1]][[0]] === Im),
						 - I/4 ( KroneckerDelta[a[[gaug+3]],d[[gaug+2]]] KroneckerDelta[b[[gaug+2]],c[[gaug+3]]] +  KroneckerDelta[a[[gaug+3]],b[[gaug+2]]] KroneckerDelta[c[[gaug+3]],d[[gaug+2]]] - 2/ListGauge[[gaug,3]] KroneckerDelta[a[[gaug+3]],c[[gaug+3]]] KroneckerDelta[b[[gaug+2]],d[[gaug+2]]]) 
						 ,
						0
					] + If[
							(RealScalarList[[a[[1]], 1]][[1]] === RealScalarList[[c[[1]], 1]][[1]] &&
							RealScalarList[[a[[1]], 1]][[0]] =!= RealScalarList[[c[[1]], 1]][[0]] &&
							RealScalarList[[a[[1]], 1]][[0]] === Im && RealScalarList[[c[[1]], 1]][[0]] === Re),
							  I/4 ( KroneckerDelta[a[[gaug+3]],d[[gaug+2]]] KroneckerDelta[b[[gaug+2]],c[[gaug+3]]] + KroneckerDelta[a[[gaug+3]],b[[gaug+2]]] KroneckerDelta[c[[gaug+3]],d[[gaug+2]]] - 2/ListGauge[[gaug,3]] KroneckerDelta[a[[gaug+3]],c[[gaug+3]]] KroneckerDelta[b[[gaug+2]],d[[gaug+2]]]) 
							,
							0
						]
			) (
				 TensorDelta[Delete[a,gaug+3][[2;;]], Delete[c,gaug+3][[2;;]]] TensorDelta[Delete[b,gaug+2][[2;;]], Delete[d,gaug+2][[2;;]]] KroneckerDelta[b[[1]], AdjWeylFermionList[[d[[1]], 3]]]
			)/;(
				ListGauge[[gaug,2]] === SU &&
				RealScalarList[[a[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				RealScalarList[[c[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[d[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]]
			),
			(** SO(N) -- all in fundamental representation *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (\[CapitalLambda][gaug][a, d, c, b])/;(
				ListGauge[[gaug,2]] === SO &&
				RealScalarList[[a[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				RealScalarList[[c[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[d[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				b[[1]] == AdjWeylFermionList[[b[[1]], 4]] && AdjWeylFermionList[[d[[1]], 3]] == b[[1]]
			),
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (
				1/4 (KroneckerDelta[a[[gaug+3]],d[[gaug+2]]] KroneckerDelta[b[[gaug+2]],c[[gaug+3]]] - KroneckerDelta[a[[gaug+3]],b[[gaug+2]]] KroneckerDelta[c[[gaug+3]],d[[gaug+2]]]) TensorDelta[Delete[a,gaug+3], Delete[c,gaug+3]] TensorDelta[Delete[b,gaug+2][[2;;]], Delete[d,gaug+2][[2;;]]] KroneckerDelta[AdjWeylFermionList[[b[[1]], 3]], d[[1]]]
			)/;(
				ListGauge[[gaug,2]] === SO &&
				RealScalarList[[a[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]] &&
				RealScalarList[[c[[1]], 3, gaug]] == ListGauge[[gaug,3]] &&
				WeylFermionList[[AdjWeylFermionList[[d[[1]], 2]], 3, gaug]] == ListGauge[[gaug,3]]
			),
			(** U(1) *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :>(
				(
					RealScalarList[[a[[1]],3,gaug]] WeylFermionList[[AdjWeylFermionList[[b[[1]], 2]], 3, gaug]]
					ComplexDelta[RealScalarList[[a[[1]],1]], RealScalarList[[c[[1]],1]]] KroneckerDelta[AdjWeylFermionList[[b[[1]], 3]], d[[1]]]
					(
						If[RealScalarList[[a[[1]],1]][[0]] === Re &&  RealScalarList[[c[[1]],1]][[0]] === Im, +1 ,
							If[RealScalarList[[a[[1]],1]][[0]] === Im &&  RealScalarList[[c[[1]],1]][[0]] === Re, -1, 0]]
					) (
						If[AdjWeylFermionList[[b[[1]], 4]] === b[[1]], -I , I] 
					) TensorDelta[a[[2;;]],c[[2;;]]] TensorDelta[b[[2;;]],d[[2;;]]] 
				)
			)/;(ListGauge[[gaug, 3]] === 1),
			(** unknown gauge group*)
			\[CapitalLambda][gaug_][a_,b_, c_, d_] :>(\[CapitalLambda][ListGauge[[gaug,1]], RealScalarList[[a[[1]],1]], AdjWeylFermionList[[b[[1]],1]], RealScalarList[[c[[1]],1]], AdjWeylFermionList[[d[[1]],1]]][a[[3+gaug]], b[[2+gaug]], c[[3+gaug]], d[[2+gaug]]] TensorDelta[a[[2;;2+gaug]], c[[2;;2+gaug]]] TensorDelta[b[[2;;1+gaug]], d[[2;;1+gaug]]] TensorDelta[a[[4+gaug;;]], c[[4+gaug;;]]]  TensorDelta[b[[3+gaug;;]], d[[3+gaug;;]]])
		}];



		(* overall multiplicity of particles / gauges *)
		FMultiplicity[f_] := WeylFermionList[[f,2]] Times@@(Function[{x},If[ListGauge[[x,3]]===1, 1, WeylFermionList[[f,3,x]]]]/@Range[NumberOfSubgroups]);
		SMultiplicity[s_] := If[s<=Length[RealScalarList], RealScalarList[[s,2,1]] RealScalarList[[s,2,2]] Times@@(Function[{x},If[ListGauge[[x,3]]===1, 1, RealScalarList[[s,3,x]]]]/@Range[NumberOfSubgroups]), 1];
		FMultiplicity[f_, g_] := If[ListGauge[[g,3]]===1, 1, WeylFermionList[[f,3,g]]];
		SMultiplicity[s_, g_] := If[s<=Length[RealScalarList], If[ListGauge[[g,3]]===1, 1, RealScalarList[[s,3,g]]], 1];
		SGaugeSinglet[s_] := And@@(If[ListGauge[[#, 3]]===1, RealScalarList[[s, 3, #]] === 0, RealScalarList[[s, 3, #]] === 1]& /@ Range[NumberOfSubgroups]);
		(* Generation contraction for Yukawa products and traces *)
		GetGenProd[symList_, sVarList_, i_, j_] := Module[
			{split, sumInd1, sumInd2},
			If[
				symList == {} || sVarList == {} || Dimensions[symList][[1]] <= 0,
				Return[0];
			];
			For[split=1, split<=Dimensions[symList][[1]], split++,
				If[
					!(MemberQ[symList[[split, 1, 2]], Mat[___], Infinity]),
					Return[Assuming[Element[sumInd1,Integers]&&(sumInd1>0)&&Element[sumInd2,Integers]&&(sumInd2>0),
						If[(split == Dimensions[symList][[1]]),
							If[split == 1,
								symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], i, j],
								Refine[ContractSum[
									((prod@@symList[[;;split-1, 1, 1]])[i,sumInd1]/.{prod[del[aa_]][i1_,i2_] :> KroneckerDelta[i1,i2]} //. { prod[A___, del[aa_], B___][C___] :> prod[A,B][C]}) Refine[Times@@(Function[{x},x[1]]/@symList[[;;split-1, 1, 2]]//.Mat:>Identity)] symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], sumInd1, j],
									{sumInd1, 1, symList[[split-1, 1, 6]]}
								]]
							],
							If[split == 1,
								Refine[ContractSum[
									symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], i, sumInd1] GetGenProd[symList[[split+1;;]], sVarList[[split+1;;]], sumInd1, j],
									{sumInd1, 1, symList[[split, 1, 6]]}
								]],
								Refine[ContractSum[
									((prod@@symList[[;;split-1, 1, 1]])[i,sumInd2]/.{prod[del[aa_]][i1_,i2_] :> KroneckerDelta[i1,i2]} //. { prod[A___, del[aa_], B___][C___] :> prod[A,B][C]}) Refine[Times@@(Function[{x},x[1]]/@symList[[;;split-1, 1, 2]]//.Mat:>Identity)] symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], sumInd2, sumInd1] GetGenProd[symList[[split+1;;]], sVarList[[split+1;;]], sumInd1, j],
									{sumInd1, 1, symList[[split, 1, 6]]},
									{sumInd2, 1, symList[[split-1, 1, 5]]}
								]]
							]
						]
					]];
				];
				If[split==Dimensions[symList][[1]], Break[];];
			];
			Return[((prod@@(symList[[All, 1, 1]]))[i,j] /.{prod[del[aa_]][i1_,i2_] :> KroneckerDelta[i1,i2]} //. {prod[A___, del[aa_], B___][C___] :> prod[A,B][C]}) Refine[Times@@(Function[{x},x[1]]/@symList[[All, 1, 2]]//.Mat:>Identity)]];
		];

		GetGenTrace[symList_, sVarList_] := Module[
			{split, sumInd1, sumInd2, sumInd3},
			If[
				symList == {} || sVarList == {} || Dimensions[symList][[1]] <= 0,
				Return[0];
			];
			For[split=1, split<=Dimensions[symList][[1]], split++,
				If[
					!(MemberQ[symList[[split, 1, 2]], Mat[___], Infinity]),
					Return[Assuming[Element[sumInd1,Integers]&&(sumInd1>0)&&Element[sumInd2,Integers]&&(sumInd2>0)&&Element[sumInd3,Integers]&&(sumInd3>0),
						If[split != Dimensions[symList][[1]],
							If[split == 1,
								Refine[ContractSum[
									symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], sumInd2, sumInd3] GetGenProd[symList[[split+1;;]], sVarList[[split+1;;]], sumInd3, sumInd2],
									{sumInd2, 1, symList[[split,1,5]]},
									{sumInd3, 1, symList[[split,1,6]]}
								]],
								Refine[ContractSum[
									((prod@@symList[[;;split-1, 1, 1]])[sumInd1,sumInd2] /.{prod[del[aa_]][i1_,i2_] :> KroneckerDelta[i1,i2]} //. { prod[A___, del[aa_], B___][C___] :> prod[A,B][C]}) Refine[Times@@(Function[{x},x[1]]/@symList[[;;split-1, 1, 2]]//.Mat:>Identity)] symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], sumInd2, sumInd3] GetGenProd[symList[[split+1;;]], sVarList[[split+1;;]], sumInd3, sumInd1],
									{sumInd1, 1, symList[[-1,1,6]]},
									{sumInd2, 1, symList[[split,1,5]]},
									{sumInd3, 1, symList[[split,1,6]]}
								]]
							],
							If[split == 1,
								Refine[ContractSum[
									symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], sumInd1, sumInd1],
									{sumInd1, 1, symList[[split,1,5]]}
								]],
								Refine[ContractSum[
									((prod@@symList[[;;split-1, 1, 1]])[sumInd1,sumInd2]/.{prod[del[aa_]][i1_,i2_] :> KroneckerDelta[i1,i2]} //. { prod[A___, del[aa_], B___][C___] :> prod[A,B][C]}) Refine[Times@@(Function[{x},x[1]]/@symList[[;;split-1, 1, 2]]//.Mat:>Identity)] symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], sumInd2, sumInd1],
									{sumInd1, 1, symList[[split,1,6]]},
									{sumInd2, 1, symList[[split,1,5]]}
								]]
							]
						]
					]];
				];
				If[split==Dimensions[symList][[1]], Break[];];
			];
			Return[(tr@@(symList[[All, 1, 1]])/.{tr[del[aa_]]:>WeylFermionList[[aa,2]]} //. {tr[AA___, del[aa_], BB___]:>tr[AA,BB]}) Refine[Times@@(Function[{x},x[1]]/@symList[[All, 1, 2]]//.Mat:>Identity)]];
		];

		(* helper function to separate matrices and contractions in fermion generations from Yukawa products *)
		Mat[A_][___] := Mat[A];


		(* optimized functions for Yukawa traces and products *)
		SolveTrace2[Y1_, Y2_, SIdx_] := Block[
			{sumInd1,sumInd2},
			ReleaseHold[SolveTrace[Y1,Y2]]//.subProd //.subYuk2 /.{
				tr[y1_, y2_]:>Times@@Join[
					{
						Refine[
							GetGenTrace[{y1, y2}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}}]//.subProd
						]
					},
					((Function[{x}, Refine[ContractSum[
						y1[[x+1,1]][SIdx[[x+1,1]], sumInd1[x], sumInd2[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd2[x], sumInd1[x]],
						{sumInd1[x], 1, y1[[x+1, 3]]},
						{sumInd2[x], 1, y1[[x+1, 4]]}
					]]]) /@ Range[NumberOfSubgroups])
				]
			}
		];

		SolveTrace3[Y1_, Y2_, Y3_, SIdx_] := Block[
			{sumInd1,sumInd2,sumInd3},
			ReleaseHold[SolveTrace[Y1,Y2,Y3]]//.subProd //.subYuk2 /.{
				tr[y1_, y2_, y3_]:>Times@@Join[
					{
						Refine[
							GetGenTrace[{y1, y2, y3}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}}]//.subProd
						]
					},
					((Function[{x}, Refine[ContractSum[
						 y1[[x+1,1]][SIdx[[x+1,1]], sumInd1[x], sumInd2[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd2[x], sumInd3[x]]  y3[[x+1, 1]][SIdx[[x+1,3]], sumInd3[x], sumInd1[x]],
						{sumInd1[x], 1, y1[[x+1, 3]]},
						{sumInd2[x], 1, y1[[x+1, 4]]},
						{sumInd3[x], 1, y3[[x+1, 3]]}
					]]]) /@ Range[NumberOfSubgroups])
				]
			}
		];

		SolveTrace4[Y1_, Y2_, Y3_, Y4_, SIdx_] := Block[
			{sumInd1,sumInd2,sumInd3, sumInd4},
			ReleaseHold[SolveTrace[Y1,Y2,Y3,Y4]]//.subProd //.subYuk2 /.{
				tr[y1_, y2_, y3_, y4_]:>Times@@Join[
					{
						Refine[
							GetGenTrace[{y1, y2, y3, y4}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}, {SIdx[[1,7]], SIdx[[1,8]]}}]//.subProd
						]
					},
					((Function[{x}, Refine[ContractSum[
						 y1[[x+1,1]][SIdx[[x+1,1]], sumInd1[x], sumInd2[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd2[x], sumInd3[x]]  y3[[x+1,1]][SIdx[[x+1,3]], sumInd3[x], sumInd4[x]] y4[[x+1,1]][SIdx[[x+1,4]], sumInd4[x], sumInd1[x]],
						{sumInd1[x], 1, y1[[x+1, 3]]},
						{sumInd2[x], 1, y1[[x+1, 4]]},
						{sumInd3[x], 1, y3[[x+1, 3]]},
						{sumInd4[x], 1, y3[[x+1, 4]]}
					]]]) /@ Range[NumberOfSubgroups])
				]
			}
		];

		SolveTrace5[Y1_, Y2_, Y3_, Y4_, Y5_, SIdx_] := Block[
			{sumInd1,sumInd2,sumInd3, sumInd4, sumInd5},
			ReleaseHold[SolveTrace[Y1,Y2,Y3,Y4,Y5]]//.subProd //.subYuk2 /.{
				tr[y1_, y2_, y3_, y4_, y5_]:>Times@@Join[
					{
						Refine[
							GetGenTrace[{y1, y2, y3, y4, y5}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}, {SIdx[[1,7]], SIdx[[1,8]]}, {SIdx[[1,9]], SIdx[[1,10]]}}]//.subProd
						]
					},
					((Function[{x}, Refine[ContractSum[
						 y1[[x+1,1]][SIdx[[x+1,1]], sumInd1[x], sumInd2[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd2[x], sumInd3[x]]  y3[[x+1,1]][SIdx[[x+1,3]], sumInd3[x], sumInd4[x]] y4[[x+1,1]][SIdx[[x+1,4]], sumInd4[x], sumInd5[x]] y5[[x+1,1]][SIdx[[x+1,5]], sumInd5[x], sumInd1[x]],
						{sumInd1[x], 1, y1[[x+1, 3]]},
						{sumInd2[x], 1, y1[[x+1, 4]]},
						{sumInd3[x], 1, y3[[x+1, 3]]},
						{sumInd4[x], 1, y3[[x+1, 4]]},
						{sumInd5[x], 1, y5[[x+1, 3]]}
					]]]) /@ Range[NumberOfSubgroups])
				]
			}
		];

		SolveTrace6[Y1_, Y2_, Y3_, Y4_, Y5_, Y6_, SIdx_] := Block[
			{sumInd1,sumInd2,sumInd3, sumInd4, sumInd5, sumInd6},
			ReleaseHold[SolveTrace[Y1,Y2,Y3,Y4,Y5,Y6]]//.subProd //.subYuk2 /.{
				tr[y1_, y2_, y3_, y4_, y5_, y6_]:>Times@@Join[
					{
						Refine[
							GetGenTrace[{y1, y2, y3, y4, y5, y6}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}, {SIdx[[1,7]], SIdx[[1,8]]}, {SIdx[[1,9]], SIdx[[1,10]]}, {SIdx[[1,11]], SIdx[[1,12]]}}]//.subProd
						]
					},
					((Function[{x}, Refine[ContractSum[
						 y1[[x+1,1]][SIdx[[x+1,1]], sumInd1[x], sumInd2[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd2[x], sumInd3[x]]  y3[[x+1,1]][SIdx[[x+1,3]], sumInd3[x], sumInd4[x]] y4[[x+1,1]][SIdx[[x+1,4]], sumInd4[x], sumInd5[x]] y5[[x+1,1]][SIdx[[x+1,5]], sumInd5[x], sumInd6[x]] y6[[x+1,1]][SIdx[[x+1,6]], sumInd6[x], sumInd1[x]],
						{sumInd1[x], 1, y1[[x+1, 3]]},
						{sumInd2[x], 1, y1[[x+1, 4]]},
						{sumInd3[x], 1, y3[[x+1, 3]]},
						{sumInd4[x], 1, y3[[x+1, 4]]},
						{sumInd5[x], 1, y5[[x+1, 3]]},
						{sumInd6[x], 1, y5[[x+1, 4]]}
					]]]) /@ Range[NumberOfSubgroups])
				]
			}
		];

		SolveProd2[Y1_, Y2_, li_, lj_, SIdx_] := Block[
			{sumInd1},
			ReleaseHold[SolveProd[Y1, Y2, li[[1]], lj[[1]]]]//.subProd //.subYuk2 /.{
				prod[y1_, y2_]:>Times@@Join[
					{
						Refine[
							GetGenProd[{y1, y2}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}}, li[[2]], lj[[2]]]//.subProd
						]
					},
					(
						Function[{x}, Refine[ContractSum[
							y1[[x+1,1]][SIdx[[x+1,1]], li[[2+x]], sumInd1[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd1[x], lj[[2+x]]],
							{sumInd1[x], 1, y2[[x+1,3]]}
						]]]/@Range[NumberOfSubgroups]
					)
				]
			}
		];

		SolveProd3[Y1_, Y2_, Y3_, li_, lj_, SIdx_] := Block[
			{sumInd1, sumInd2},
			ReleaseHold[SolveProd[Y1, Y2, Y3, li[[1]], lj[[1]]]]//.subProd //.subYuk2 /.{
				prod[y1_, y2_, y3_]:>Times@@Join[
					{
						Refine[
							GetGenProd[{y1, y2, y3}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}}, li[[2]], lj[[2]]]//.subProd
						]
					},
					(
						Function[{x}, Refine[ContractSum[
							y1[[x+1,1]][SIdx[[x+1,1]], li[[2+x]], sumInd1[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd1[x], sumInd2[x]] y3[[x+1,1]][SIdx[[x+1,3]], sumInd2[x], lj[[2+x]]],
							{sumInd1[x], 1, y2[[x+1,3]]},
							{sumInd2[x], 1, y2[[x+1,4]]}
						]]]/@Range[NumberOfSubgroups]
					)
				]
			}
		];

		SolveProd4[Y1_, Y2_, Y3_, Y4_, li_, lj_, SIdx_] := Block[
			{sumInd1, sumInd2, sumInd3},
			ReleaseHold[SolveProd[Y1, Y2, Y3, Y4, li[[1]], lj[[1]]]]//.subProd //.subYuk2 /.{
				prod[y1_, y2_, y3_, y4_]:>Times@@Join[
					{
						Refine[
							GetGenProd[{y1, y2, y3, y4}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}, {SIdx[[1,7]],SIdx[[1,8]]}}, li[[2]], lj[[2]]]//.subProd
						]
					},
					(
						Function[{x}, Refine[ContractSum[
							y1[[x+1,1]][SIdx[[x+1,1]], li[[2+x]], sumInd1[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd1[x], sumInd2[x]] y3[[x+1,1]][SIdx[[x+1,3]], sumInd2[x], sumInd3[x]] y4[[x+1,1]][SIdx[[x+1,4]], sumInd3[x], lj[[2+x]]],
							{sumInd1[x], 1, y2[[x+1,3]]},
							{sumInd2[x], 1, y2[[x+1,4]]},
							{sumInd3[x], 1, y4[[x+1,3]]}
						]]]/@Range[NumberOfSubgroups]
					)
				]
			}
		];

		SolveProd5[Y1_, Y2_, Y3_, Y4_, Y5_, li_, lj_, SIdx_] := Block[
			{sumInd1, sumInd2, sumInd3, sumInd4},
			ReleaseHold[SolveProd[Y1, Y2, Y3, Y4, Y5, li[[1]], lj[[1]]]]//.subProd //.subYuk2 /.{
				prod[y1_, y2_, y3_, y4_, y5_]:>Times@@Join[
					{
						Refine[
							GetGenProd[{y1, y2, y3, y4, y5}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}, {SIdx[[1,7]],SIdx[[1,8]]}, {SIdx[[1,9]], SIdx[[1,10]]}}, li[[2]], lj[[2]]]//.subProd
						]
					},
					(
						Function[{x}, Refine[ContractSum[
							y1[[x+1,1]][SIdx[[x+1,1]], li[[2+x]], sumInd1[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd1[x], sumInd2[x]] y3[[x+1,1]][SIdx[[x+1,3]], sumInd2[x], sumInd3[x]] y4[[x+1,1]][SIdx[[x+1,4]], sumInd3[x], sumInd4[x]] y5[[x+1,1]][SIdx[[x+1,5]], sumInd4[x], lj[[2+x]]],
							{sumInd1[x], 1, y2[[x+1,3]]},
							{sumInd2[x], 1, y2[[x+1,4]]},
							{sumInd3[x], 1, y4[[x+1,3]]},
							{sumInd4[x], 1, y4[[x+1,4]]}
						]]]/@Range[NumberOfSubgroups]
					)
				]
			}
		];

		SolveSProd2[L1_, L2_, SIdx_] := Block[
			{},
			ReleaseHold[prod[L1, L2]/.subQuart1//.subProd]//.subQuart2/.{
				prod[l1_, l2_] :> Times@@Join[
					{
						l1[[1,1]] l2[[1,1]] l1[[1,2]][SIdx[[1,1]], SIdx[[1,2]], SIdx[[1,3]], SIdx[[1,4]], SIdx[[1,5]], SIdx[[1,6]], SIdx[[1,7]], SIdx[[1,8]]] l2[[1,2]][SIdx[[1,9]], SIdx[[1,10]], SIdx[[1,11]], SIdx[[1,12]], SIdx[[1,13]], SIdx[[1,14]], SIdx[[1,15]], SIdx[[1,16]]]
					},
					Function[{x},
						l1[[x+1,1]][SIdx[[1+x,1]], SIdx[[1+x,2]], SIdx[[1+x,3]], SIdx[[1+x,4]]] l2[[x+1,1]][SIdx[[1+x,5]], SIdx[[1+x,6]], SIdx[[1+x,7]], SIdx[[1+x,8]]]
					]/@Range[NumberOfSubgroups]
				]
			}
		];

		SolveSProd3[L1_, L2_, L3_, SIdx_] := Block[
			{},
			ReleaseHold[prod[L1, L2, L3]/.subQuart1//.subProd]//.subQuart2/.{
				prod[l1_, l2_, l3_] :> Times@@Join[
					{
						l1[[1,1]] l2[[1,1]] l3[[1,1]] l1[[1,2]][SIdx[[1,1]], SIdx[[1,2]], SIdx[[1,3]], SIdx[[1,4]], SIdx[[1,5]], SIdx[[1,6]], SIdx[[1,7]], SIdx[[1,8]]] l2[[1,2]][SIdx[[1,9]], SIdx[[1,10]], SIdx[[1,11]], SIdx[[1,12]], SIdx[[1,13]], SIdx[[1,14]], SIdx[[1,15]], SIdx[[1,16]]] l3[[1,2]][SIdx[[1,17]], SIdx[[1,18]], SIdx[[1,19]], SIdx[[1,20]], SIdx[[1,21]], SIdx[[1,22]], SIdx[[1,23]], SIdx[[1,24]]]
					},
					Function[{x},
						l1[[x+1,1]][SIdx[[1+x,1]], SIdx[[1+x,2]], SIdx[[1+x,3]], SIdx[[1+x,4]]] l2[[x+1,1]][SIdx[[1+x,5]], SIdx[[1+x,6]], SIdx[[1+x,7]], SIdx[[1+x,8]]] l3[[x+1,1]][SIdx[[1+x,9]], SIdx[[1+x,10]], SIdx[[1+x,11]], SIdx[[1+x,12]]]
					]/@Range[NumberOfSubgroups]
				]
			}
		];


		(* traces and products of fermion type indices *)
		SolveProd[i1_, i2_] := KroneckerDelta[AdjWeylFermionList[[i1,3]], i2];
		SolveProd[a_, i1_, i2_] := prod[a[i1,i2]]  //. {adj[A_][ii1_, ii2_] :> adj[A[ii2, ii1]]} /.subYuk1 //.subProd;
		SolveProd[a_,b___, i1_, i2_] := Sum[ (prod[a[i1, s], SolveProdHold[b, AdjWeylFermionList[[s,3]], i2]] //. {adj[A_][ii1_, ii2_] :> adj[A[ii2, ii1]]} /.subYuk1 //.subProd /. SolveProdHold -> SolveProd), {s, 1, Length[AdjWeylFermionList]}];
		SolveTrace[a___] := Sum[ (tr[SolveProd[a, AdjWeylFermionList[[s,3]], s]] //.subProd), {s, 1, Length[AdjWeylFermionList]}];

		(* permutations *)
		Perm[f_[a_,b_,c_,d_]]:= f[a,b,c,d] + f[a,b,d,c] + f[a,c,b,d] + f[a,c,d,b] + f[a,d,b,c] + f[a,d,c,b] + f[b,a,c,d] + f[b,a,d,c] + f[b,c,a,d] + f[b,c,d,a] + f[b,d,a,c] + f[b,d,c,a] + f[c,a,b,d] + f[c,a,d,b] + f[c,b,a,d] + f[c,b,d,a] + f[c,d,a,b] + f[c,d,b,a] + f[d,a,b,c] + f[d,a,c,b] + f[d,b,a,c] + f[d,b,c,a] + f[d,c,a,b] + f[d,c,b,a];
		PermList[f_[a_,b_,c_,d_]]:={f[a,b,c,d], f[a,b,d,c], f[a,c,b,d], f[a,c,d,b], f[a,d,b,c], f[a,d,c,b], f[b,a,c,d], f[b,a,d,c], f[b,c,a,d], f[b,c,d,a], f[b,d,a,c], f[b,d,c,a], f[c,a,b,d], f[c,a,d,b], f[c,b,a,d], f[c,b,d,a], f[c,d,a,b], f[c,d,b,a], f[d,a,b,c], f[d,a,c,b], f[d,b,a,c], f[d,b,c,a], f[d,c,a,b], f[d,c,b,a]};
		PermList[s_ f_[a_,b_,c_,d_]]:={s f[a,b,c,d], s f[a,b,d,c], s f[a,c,b,d], s f[a,c,d,b], s f[a,d,b,c], s f[a,d,c,b], s f[b,a,c,d], s f[b,a,d,c], s f[b,c,a,d], s f[b,c,d,a], s f[b,d,a,c], s f[b,d,c,a], s f[c,a,b,d], s f[c,a,d,b], s f[c,b,a,d], s f[c,b,d,a], s f[c,d,a,b], s f[c,d,b,a], s f[d,a,b,c], s f[d,a,c,b], s f[d,b,a,c], s f[d,b,c,a], s f[d,c,a,b], s f[d,c,b,a]};


		(* workaround a mathematica bug *)
		ListPosition[A_, B___] := Position[A//. {{} -> $EMPTYLIST}, B];

		(* Define Sum that resolves all KroneckerDelta[__] and Generators before it does the summation *)
		subSum := {
			A_ SimplifySum[B_, C___] :> SimplifySum[A B, C],
			SimplifySum[A_ + B_, C___] :> SimplifySum[A, C] + SimplifySum[B, C],
			SimplifySum[D_ (A_ + B_), C___] :> SimplifySum[D A, C] + SimplifySum[D B, C],
			SimplifySum[SimplifySum[A_, B___], C___] :> SimplifySum[A, B, C],
			SimplifySum[A_, SS1___, {aa_, 1, 1}, SS2___] :> SimplifySum[A//.{aa->1}, SS1, SS2],
			Conjugate[KroneckerDelta[A___]] :> KroneckerDelta[A],
			Conjugate[B_ KroneckerDelta[A___]] :> Conjugate[B] KroneckerDelta[A],
			SimplifySum[A_ KroneckerDelta[aa_, bb_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[A //. aa->bb , SS1, SS2],
			SimplifySum[KroneckerDelta[aa_, bb_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[1 , SS1, SS2],
			SimplifySum[A_ KroneckerDelta[bb_, aa_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[A //. aa->bb , SS1, SS2],
			SimplifySum[KroneckerDelta[bb_, aa_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[1 , SS1, SS2],
			Power[KroneckerDelta[A___], a_] :> KroneckerDelta[A],
			SimplifySum[c_, ss1___, {p_, 1, q_}, ss2___ ] :> SimplifySum[q c, ss1, ss2] /; !MemberQ[{c, ss1, ss2}, p, Infinity],
			Conjugate[Generator[A___][a_, i_, j_]] :> Generator[A][a, j, i],
			SimplifySum[C_ Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {a_, 1, aa_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[C C2[A] KroneckerDelta[i, k], SS1, SS2, SS3],
			SimplifySum[C_ Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {j_, 1, jj_}, SS2___, {a_, 1, aa_}, SS3___] :> SimplifySum[C C2[A] KroneckerDelta[i, k], SS1, SS2, SS3],
			SimplifySum[Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {a_, 1, aa_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[C2[A] KroneckerDelta[i, k], SS1, SS2, SS3],
			SimplifySum[Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {j_, 1, jj_}, SS2___, {a_, 1, aa_}, SS3___] :> SimplifySum[C2[A] KroneckerDelta[i, k], SS1, SS2, SS3],
			SimplifySum[C_ Generator[A___][a_, i_, j_] Generator[A___][b_, j_, i_], SS1___, {i_, 1, ii_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[C T2[A]KroneckerDelta[a, b], SS1, SS2, SS3],
			SimplifySum[Generator[A___][a_, i_, j_] Generator[A___][b_, j_, i_], SS1___, {i_, 1, ii_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[T2[A] KroneckerDelta[a, b], SS1, SS2, SS3],
			SimplifySum[A_] :> A,
			SimplifySum[] :> 0
		};

		(* like subSum, but with more advanced simplifications to be utilized in SimplifyProduct *)
		subSum2 := {
			A_ SimplifySum[B_, C___] :> SimplifySum[A B, C],
			SimplifySum[A_ + B_, C___] :> SimplifySum[A, C] + SimplifySum[B, C],
			SimplifySum[D_ (A_ + B_), C___] :> SimplifySum[D A, C] + SimplifySum[D B, C],
			SimplifySum[SimplifySum[A_, B___], C___] :> SimplifySum[A, B, C],
			SimplifySum[A_, SS1___, {aa_, 1, 1}, SS2___] :> SimplifySum[A//.{aa->1}, SS1, SS2],
			Conjugate[KroneckerDelta[A___]] :> KroneckerDelta[A],
			Conjugate[B_ KroneckerDelta[A___]] :> Conjugate[B] KroneckerDelta[A],
			SimplifySum[A_ KroneckerDelta[aa_, bb_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[A //. aa->bb , SS1, SS2],
			SimplifySum[KroneckerDelta[aa_, bb_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[1 , SS1, SS2],
			SimplifySum[A_ KroneckerDelta[bb_, aa_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[A //. aa->bb , SS1, SS2],
			SimplifySum[KroneckerDelta[bb_, aa_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[1 , SS1, SS2],
			Power[KroneckerDelta[A___], a_] :> KroneckerDelta[A],
			SimplifySum[c_, ss1___, {p_, 1, q_}, ss2___ ] :> SimplifySum[q c, ss1, ss2] /; !MemberQ[{c, ss1, ss2}, p, Infinity],
			Conjugate[Generator[A___][a_, i_, j_]] :> Generator[A][a, j, i],
			SimplifySum[C_ Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {a_, 1, aa_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[C C2[A] KroneckerDelta[i, k], SS1, SS2, SS3],
			SimplifySum[C_ Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {j_, 1, jj_}, SS2___, {a_, 1, aa_}, SS3___] :> SimplifySum[C C2[A] KroneckerDelta[i, k], SS1, SS2, SS3],
			SimplifySum[Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {a_, 1, aa_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[C2[A] KroneckerDelta[i, k], SS1, SS2, SS3],
			SimplifySum[Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {j_, 1, jj_}, SS2___, {a_, 1, aa_}, SS3___] :> SimplifySum[C2[A] KroneckerDelta[i, k], SS1, SS2, SS3],
			SimplifySum[C_ Generator[A___][a_, i_, j_] Generator[A___][b_, j_, i_], SS1___, {i_, 1, ii_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[C T2[A]KroneckerDelta[a, b], SS1, SS2, SS3],
			SimplifySum[Generator[A___][a_, i_, j_] Generator[A___][b_, j_, i_], SS1___, {i_, 1, ii_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[T2[A] KroneckerDelta[a, b], SS1, SS2, SS3],
			SimplifySum[C_ Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {j_, 1, jj_}, SS2___, {k_, 1, kk_}, SS3___, {a_, 1, aa_}, SS4___] :> SimplifySum[C (C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[C_ Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {k_, 1, kk_}, SS2___, {j_, 1, jj_}, SS3___, {a_, 1, aa_}, SS4___] :> SimplifySum[C (C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {j_, 1, jj_}, SS2___, {k_, 1, kk_}, SS3___, {a_, 1, aa_}, SS4___] :> SimplifySum[(C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {k_, 1, kk_}, SS2___, {j_, 1, jj_}, SS3___, {a_, 1, aa_}, SS4___] :> SimplifySum[(C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[C_ Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {a_, 1, aa_}, SS2___, {k_, 1, kk_}, SS3___, {j_, 1, jj_}, SS4___] :> SimplifySum[C (C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[C_ Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {a_, 1, aa_}, SS2___, {j_, 1, jj_}, SS3___, {k_, 1, kk_}, SS4___] :> SimplifySum[C (C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {a_, 1, aa_}, SS2___, {k_, 1, kk_}, SS3___, {j_, 1, jj_}, SS4___] :> SimplifySum[(C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {a_, 1, aa_}, SS2___, {j_, 1, jj_}, SS3___, {k_, 1, kk_}, SS4___] :> SimplifySum[(C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[C_ Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {j_, 1, jj_}, SS2___, {a_, 1, aa_}, SS3___, {k_, 1, kk_}, SS4___] :> SimplifySum[C (C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[C_ Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {k_, 1, kk_}, SS2___, {a_, 1, aa_}, SS3___, {j_, 1, jj_}, SS4___] :> SimplifySum[C (C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {j_, 1, jj_}, SS2___, {a_, 1, aa_}, SS3___, {k_, 1, kk_}, SS4___] :> SimplifySum[(C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {k_, 1, kk_}, SS2___, {a_, 1, aa_}, SS3___, {j_, 1, jj_}, SS4___] :> SimplifySum[(C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[C_ Conjugate[B_ \[CapitalLambda][g_, p1_, p2_, p3_, p4_][i1_, i2_, i3_, i4_]], SS1___] :> SimplifySum[C Conjugate[B] \[CapitalLambda][g, p3, p4, p1, p2][i3, i4, i1, i2], SS1],
			SimplifySum[C_ Conjugate[\[CapitalLambda][g_, p1_, p2_, p3_, p4_][i1_, i2_, i3_, i4_]], SS1___] :> SimplifySum[C \[CapitalLambda][g, p3, p4, p1, p2][i3, i4, i1, i2], SS1],
			SimplifySum[Conjugate[B_ \[CapitalLambda][g_, p1_, p2_, p3_, p4_][i1_, i2_, i3_, i4_]], SS1___] :> SimplifySum[Conjugate[B] \[CapitalLambda][g, p3, p4, p1, p2][i3, i4, i1, i2], SS1],
			SimplifySum[Conjugate[\[CapitalLambda][g_, p1_, p2_, p3_, p4_][i1_, i2_, i3_, i4_]], SS1___] :> SimplifySum[\[CapitalLambda][g, p3, p4, p1, p2][i3, i4, i1, i2], SS1],
			SimplifySum[C_ \[CapitalLambda][g_, ferm_, ferm_, conj[ferm_], conj[ferm_]][b_, a_, a_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[\[CapitalLambda][g_, ferm_, ferm_, conj[ferm_], conj[ferm_]][b_, a_, a_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[C_ \[CapitalLambda][g_, conj[ferm_], conj[ferm_], ferm_, ferm_][b_, a_, a_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[\[CapitalLambda][g_, conj[ferm_], conj[ferm_], ferm_, ferm_][b_, a_, a_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[C_ \[CapitalLambda][g_, ferm_, ferm_, conj[ferm_], conj[ferm_]][a_, b_, c_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[\[CapitalLambda][g_, ferm_, ferm_, conj[ferm_], conj[ferm_]][a_, b_, c_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[C_ \[CapitalLambda][g_, conj[ferm_], conj[ferm_], ferm_, ferm_][a_, b_, c_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[\[CapitalLambda][g_, conj[ferm_], conj[ferm_], ferm_, ferm_][a_, b_, c_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[C_ \[CapitalLambda][g_, ferm_, conj[ferm_], conj[ferm_], ferm_][b_, c_, a_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[\[CapitalLambda][g_, ferm_, conj[ferm_], conj[ferm_], ferm_][b_, c_, a_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[C_ \[CapitalLambda][g_, ferm_, conj[ferm_], conj[ferm_], ferm_][a_, a_, b_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[\[CapitalLambda][g_, ferm_, conj[ferm_], conj[ferm_], ferm_][a_, a_, b_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[C_ \[CapitalLambda][g_, conj[ferm_], ferm_, ferm_, conj[ferm_]][b_, c_, a_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[\[CapitalLambda][g_, conj[ferm_], ferm_, ferm_, conj[ferm_]][b_, c_, a_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[C_ \[CapitalLambda][g_, conj[ferm_], ferm_, ferm_, conj[ferm_]][a_, a_, b_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[\[CapitalLambda][g_, conj[ferm_], ferm_, ferm_, conj[ferm_]][a_, a_, b_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C2[ferm, g] KroneckerDelta[b,c], SS1, SS2] /; (MemberQ[WeylFermionList[[;;,1]], ferm]),
			SimplifySum[A_] :> A,
			SimplifySum[] :> 0
		};

		DisableNativeSums[disable_:True] := If[
			disable,
			ContractSum[A_] := Refine[A //.Join[subSum,subSimplifySum]];
			ContractSum[A_, B__] := Refine[
				SimplifySum[Expand[A],B]//.Join[subSum,subSimplifySum]];
			ContractSum2[A_] := Refine[A //.Join[subSum2,subSimplifySum]];
			ContractSum2[A_, B__] := Refine[SimplifySum[Expand[A],B]//.Join[subSum2,subSimplifySum]];,
			ContractSum[A_] := Refine[A //.Join[subSum,subSimplifySum] /.SimplifySum -> Sum];
			ContractSum[A_, B__] := Refine[
				(SimplifySum[Expand[A],B]//.Join[subSum,subSimplifySum])/.SimplifySum -> Sum
			];
			ContractSum2[A_] := Refine[A //.Join[subSum2,subSimplifySum] /.SimplifySum -> Sum];
			ContractSum2[A_, B__] := Refine[
				(SimplifySum[Expand[A],B]//.Join[subSum2,subSimplifySum])/.SimplifySum -> Sum
			];
		];

		ExtractIndexStructure[exp_, pamlist_] := (
			(Factorize[1, #]& /@Flatten[{Expand[exp]/.Plus->List}])//.{
				Factorize[A_, B_ C_] :> Factorize[A B, C] /; (And @@ (FreeQ[B, #, Infinity] & /@ pamlist)),
				Factorize[A_, B_ ] :> Factorize[A B, 1] /; (And @@ (FreeQ[B, #, Infinity] & /@ pamlist))
			} //. {
				{FF1___, Factorize[A_, B_], FF2___, Factorize[C_, B_], FF3___} :> {FF1, Factorize[A + C, B], FF2, FF3},
				{FF1__, Factorize[0, A_], FF2___} :> {FF1, FF2},
				{FF1___, Factorize[0, A_], FF2__} :> {FF1, FF2}
			}
		);

		ApplyDistribute[func_, unexp_] := Block[
			{exp = Expand[unexp]},
			If[exp[[0]] === Plus, 
				func /@ exp,
				func[exp]
			]
		];

		(* Error Messages *)
		Gauge::RepMismatch = "Representation list does not match number of subgroups";
		Gauge::NAN = "Number of subgroups is corrupted";
		Gauge::Full = "Number of gauge subgroups exceeds initial definition";
		Gauge::RepInvalid = "Invalid input for gauge indices";
		Gen::RepInvalid = "Invalid input for generation indices";
		WeylFermion::RepMismatch = "Representation list does not match number of subgroups";
		RealScalar::RepMismatch = "Representation list does not match number of subgroups";
		Yukawa::ContractionError = "Number of gauge contractions does not match number of subgroups";
		Yukawa::UnknownParticle = "Undefined particle in Yukawa sector";
		Quartic::ContractionError = "Number of gauge contractions does not match number of subgroups";
		Scalar::UnknownParticle = "Undefined Scalar field";
		Fermion::UnknownParticle = "Undefined Fermion field";

		Reset[];
	End[];
EndPackage[];
