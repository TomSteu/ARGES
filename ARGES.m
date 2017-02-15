BeginPackage["ARGES`"];
	Gauge::usage = "Specify gauge subgroup by Gauge[coupling, Group[N], {Representation1, ...}];";
	WeylFermion::usage = "Add Weyl fermion by WeylFermion[symbol, Flavors, {Representation1, ...}]";
	RealScalar::usage = "Add real scalar by RealScalar[symbol, Flavors, {Representation1, ...}]";
	ComplexScalar::usage = "Add complex scalar by ComplexScalar[Symbol, Flavors, {Representation1, ...}]; this adds the real scalars Re[Symbol] and Im[Symbol]";
	YukawaYaij::usage = "Add Yukawa matrix term (with h.c.) YukawaYaij[Symbol, ScalarField, LeftFermion, RightFermion, {List of contractions for each gauge}, factor]; Contractions are functions [ScalarIndex, LeftFermionIndex, RightFermionIndex], example: Yaijk[y, S, F1, F2, ...] == -  factor y adj[F1].S.F2 + h.c.";
	YukawaY::usage = "Add Yukawa term (with h.c.) and specify generation contraction: YukawaYaij[Symbol, ScalarField, LeftFermion, RightFermion, {List of contractions for each gauge}, (contraction of flavors)[ScalarFieldGen_, LeftFermionGen_, RightFermionGen_]];"
	Quartic\[Lambda]abcd::usage = "Add scalar quartic coupling Quartic\[Lambda]abcd[Symbol, Scalar1, Scalar2, Scalar3, Scalar4, {List of contractions for each gauge}, prefactor and contraction of flavors], complex scalars will be rewritten as real and imaginary part and the quartic is symmetrized totally automatically. No additional 1/4! will be added to the prefactor, but there might be a factor to keep the norm after symmetrization";
	\[Beta]::usage = "Display coupling (LoopLevel = 0) or Beta function for gauge coupling \[Beta][Gauge, LoopLevel];, Yukawa-like couplings \[Beta][ScalarField, FermionField1, FermionField2, {scalar generation, scalar gauge1, ... }, ..., LoopLevel]; and symmetrized quartic scalar couplings \[Beta][Scalar1, Scalar2, Scalar3, Scalar4, {Scalar1 generation, Scalar1 gauge1, ...}, ... LoopLevel];";
	Reset::usage = "reset/initiate package";
	ComputeInvariants::usage = "Calculates known invariants for beta functions, saves them as rules in subInvariants";
	subInvariants::usage = "containts replacement rules for beta function invariants, use ComputeInvariants[] to calculate";
	GetGauge::usage = "Returns representation / charge for particle";
	SimplifyProduct::usage = "Simplifies tr[___] and prod[___] expressions";
	F::usage = "fermionic";
	S::usage = "scalar";
	Y::usage = "Yukawa";
	d::usage="Dimension of Representation";
	C2::usage = "Casimir Invariant";
	S2::usage = "Dynkin Index";
	Y2::usage = "Yukawa Invariant";
	Y4::usage = "Yukawa Invariant";
	prod::usage = "product of flavour matrices";
	adj::usage = "adjoint";
	tr::usage = "trace of flavour matrices";
	U::usage = "Unitary Group";
	SU::usage = "Special Unitary Group";
	SO::usage = "Special Orthogonal Group";
	

	
	Sqr[x_] := x*x;
	subAlpha = {\[Alpha][g_] :> Sqr[g/(4 \[Pi])]};
	NumberOfSubgroups = 1;

	
 	(*Begin["Private`"];*)
		Reset[] := Module[
			{},
			ListGauge = {};
			ListYukawa = {};
			ListQuartic = {};
			ListQuarticSym = {};
			WeylFermionList = {};
			RealScalarList = {};
			ComplexScalarList = {};
			subInvariants = {};
			$Assumptions = Element[KroneckerDelta[___], Reals];
		];

		(* Interfaces to define the theory *)
		Gauge[sym_, group_, n_, reps_List] := Module[
			{},
			If[Dimensions[reps][[1]] != NumberOfSubgroups,
				Message[Gauge::RepMismatch];,
				If[!NumberQ[n], $Assumptions=$Assumptions&&(n>1)&&Element[n,Integers]];
				ListGauge = Append[ListGauge, {sym, group, n, reps}];

			];
		];
		
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
			posP = ListPosition[WeylFermionList,_List?(#[[1]] == part &)];
			If[posP != 0,
				Return[WeylFermionList[[posP[[1,1]], 3, posG]]];
			];
			Return[0];
		];
		
		SimplifyProduct[term_] := (term //. subProd //.{tr[adj[a_], b_] :> tr[b, adj[a]], tr[adj[a_], b_, adj[c_], d_]:>tr[b, adj[c], d, adj[a]], tr[adj[a_], b_, adj[c_], d_, adj[e_], f_]:>tr[b, adj[c], d, adj[e], f, adj[a]], (A_ tr[C___, a_, adj[b_], G___, c_, adj[d_], F___] + B_ tr[G___, c_, adj[d_], F___, C___, a_, adj[b_]]) :> (A+B)tr[C, a, adj[b], G, c, adj[d], F], (A_ tr[C___, a_, adj[b_], G___, c_, adj[d_], F___] + B_ tr[c_, adj[d_], F___, C___, a_, adj[b_], G___]) :> (A+B)tr[C, a, adj[b], G, c, adj[d], F]});
		
		WeylFermion[sym_, Nflavor_, Gauge_List] := Module[
			{},
			If[Dimensions[Gauge][[1]] != NumberOfSubgroups, 
				Message[WeylFermion::RepMismatch];,
				If[!NumberQ[Nflavor], $Assumptions=$Assumptions&&Element[Nflavor,Integers]&&(Nflavor>=0)];
				WeylFermionList = Append[WeylFermionList, {sym, Nflavor, Gauge}];
			];
		];
		
		RealScalar[sym_, Nflavor_List, Gauge_List] := Module[
			{},
			If[Dimensions[Gauge][[1]] != NumberOfSubgroups || Dimensions[Nflavor][[1]] != 2, 
				Message[RealScalar::RepMismatch];,
				If[!NumberQ[Nflavor[[1]]], $Assumptions=$Assumptions&&Element[Nflavor[[1]],Integers]&&(Nflavor[[1]]>=0)];
				If[!NumberQ[Nflavor[[1]]], $Assumptions=$Assumptions&&Element[Nflavor[[1]],Integers]&&(Nflavor[[1]]>=0)];
				RealScalarList = Append[RealScalarList, {sym, Nflavor, Gauge}];
			];
		];
		
		ComplexScalar[sym_, Nflavor_, Gauge_List] := Module[
			{},
			ComplexScalarList = Append[ComplexScalarList, sym];
			RealScalar[Re[sym], Nflavor, Gauge];
			RealScalar[Im[sym], Nflavor, Gauge];
		];
		
		YukawaYaij[sym_, Sa_, Fi_, Fj_, gauge_List, fak_:1] := Module[
			{posS, posFi, posFj},
			If[Dimensions[gauge][[1]] != NumberOfSubgroups,
				Message[Yukawa::ContractionError];
				Return[];
			];
			posS  = ListPosition[ComplexScalarList, Sa];
			If[posS != {},
				YukawaYaij[sym, Re[Sa], Fi, Fj, gauge, fak/Sqrt[2]];
				YukawaYaij[sym, Im[Sa], Fi, Fj, gauge, I fak/Sqrt[2]];
				Return[];
			];
			posS  = ListPosition[adj/@ComplexScalarList, Sa];
			If[posS != {},
				YukawaYaij[sym, Re[Sa[[1]]], Fi, Fj, gauge, fak/Sqrt[2]];
				YukawaYaij[sym, Im[Sa[[1]]], Fi, Fj, gauge, -I fak/Sqrt[2]];
				Return[];
			];
			posS  = ListPosition[RealScalarList,_List?(#[[1]] == Sa &)];
			posFi = ListPosition[WeylFermionList,_List?(#[[1]] == Fi &)];
			posFj = ListPosition[WeylFermionList,_List?(#[[1]] == Fj &)];
			If[posS == {} || posFi == {} || posFj == {},
				Message[Yukawa::UnknownParticle];,
				ListYukawa = Append[ListYukawa,{sym, posS[[1,1]], posFi[[1,1]], posFj[[1,1]], gauge, Mat[fak]&}];
			];
		];
		
		YukawaY[sym_, Sa_, Fi_, Fj_, gauge_List, fak_] := Module[
			{posS, posFi, posFj},
			If[Dimensions[gauge][[1]] != NumberOfSubgroups,
				Message[Yukawa::ContractionError];
				Return[];
			];
			posS  = ListPosition[ComplexScalarList, Sa];
			If[posS != {},
				YukawaY[sym, Re[Sa], Fi, Fj, gauge, Evaluate[fak[#1,#2,#3,#4]/Sqrt[2]]&];
				YukawaY[sym, Im[Sa], Fi, Fj, gauge, Evaluate[I fak[#1,#2,#3,#4]/Sqrt[2]]&];
				Return[];
			];
			posS  = ListPosition[adj/@ComplexScalarList, Sa];
			If[posS != {},
				YukawaY[sym, Re[Sa[[1]]], Fi, Fj, gauge, Evaluate[fak[#2,#1,#3,#4]/Sqrt[2]]&];
				YukawaY[sym, Im[Sa[[1]]], Fi, Fj, gauge, Evaluate[-I fak[#2,#1,#3,#4]/Sqrt[2]]&];
				Return[];
			];
			posS  = ListPosition[RealScalarList,_List?(#[[1]] == Sa &)];
			posFi = ListPosition[WeylFermionList,_List?(#[[1]] == Fi &)];
			posFj = ListPosition[WeylFermionList,_List?(#[[1]] == Fj &)];
			If[posS == {} || posFi == {} || posFj == {},
				Message[Yukawa::UnknownParticle];,
				ListYukawa = Append[ListYukawa,{sym, posS[[1,1]], posFi[[1,1]], posFj[[1,1]], gauge, fak}];
			];
		];
		
		Quartic\[Lambda]abcd[sym_, Sa_, Sb_, Sc_, Sd_, gauge_List, fak_:(1&)] := Module[
			{posA, posB, posC, posD, permList, permListPos, iter, x, x2, perm1, perm2, perm3, perm4},
			posA = ListPosition[adj/@ComplexScalarList, Sa];
			If[posA != {},
				posB = ListPosition[ComplexScalarList, Sb];
				If[posB != {} && posB == posA,
					Quartic\[Lambda]abcd[sym, Re[Sa[[1]]], Re[Sb], Sc, Sd, gauge, (1/2 fak[#2,#1,#3,#4,#5,#6,#7,#8])&];
					Quartic\[Lambda]abcd[sym, Im[Sa[[1]]], Im[Sb], Sc, Sd, gauge, (1/2 fak[#2,#1,#3,#4,#5,#6,#7,#8])&];
					Return[];
				];
				Quartic\[Lambda]abcd[sym, Re[Sa[[1]]], Sb, Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Quartic\[Lambda]abcd[sym, Im[Sa[[1]]], Sb, Sc, Sd, gauge, (-1/Sqrt[2]fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Return[];
			];
			posA = ListPosition[ComplexScalarList, Sa];
			If[posA != {},
				posB = ListPosition[adj/@ComplexScalarList, Sb];
				If[posB != {} && posA == posB,
					Quartic\[Lambda]abcd[sym, Re[Sa], Re[Sb[[1]]], Sc, Sd, gauge, (1/2 fak[#1,#2,#4,#3,#5,#6,#7,#8])&];
					Quartic\[Lambda]abcd[sym, Im[Sa], Im[Sb[[1]]], Sc, Sd, gauge, (1/2 fak[#1,#2,#4,#3,#5,#6,#7,#8])&];
					Return[];
				];
				Quartic\[Lambda]abcd[sym, Re[Sa], Sb, Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Quartic\[Lambda]abcd[sym, Im[Sa], Sb, Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Return[];
			];
			posB = ListPosition[adj/@ComplexScalarList, Sb];
			If[posB != {},
				posC = ListPosition[ComplexScalarList, Sc];
				If[posC != {} && posB == posC,
					Quartic\[Lambda]abcd[sym, Sa, Re[Sb[[1]]], Re[Sc], Sd, gauge, (1/2 fak[#1,#2,#4,#3,#5,#6,#7,#8])&];
					Quartic\[Lambda]abcd[sym, Sa, Im[Sb[[1]]], Im[Sc], Sd, gauge, (1/2 fak[#1,#2,#4,#3,#5,#6,#7,#8])&];
					Return[];
				];
				Quartic\[Lambda]abcd[sym, Sa, Re[Sb[[1]]], Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#4,#3,#5,#6,#7,#8])&];
				Quartic\[Lambda]abcd[sym, Sa, Im[Sb[[1]]], Sc, Sd, gauge, (-1/Sqrt[2] fak[#1,#2,#4,#3,#5,#6,#7,#8])&];
				Return[];
			];
			posB = ListPosition[ComplexScalarList, Sb];
			If[posB != {},
				posC = ListPosition[adj/@ComplexScalarList, Sc];
				If[posC != {} && posB == posC,
					Quartic\[Lambda]abcd[sym, Sa, Re[Sb], Re[Sc[[1]]], Sd, gauge, (1/2 fak[#1,#2,#3,#4,#6,#5,#7,#8])&];
					Quartic\[Lambda]abcd[sym, Sa, Im[Sb], Im[Sc[[1]]], Sd, gauge, (1/2 fak[#1,#2,#3,#4,#6,#5,#7,#8])&];
					Return[];
				];
				Quartic\[Lambda]abcd[sym, Sa, Re[Sb], Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Quartic\[Lambda]abcd[sym, Sa, Im[Sb], Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Return[];
			];
			posC = ListPosition[adj/@ComplexScalarList, Sc];
			If[posC != {},
				posD = ListPosition[ComplexScalarList, Sd];
				If[posD != {} && posC == posD,
					Quartic\[Lambda]abcd[sym, Sa, Sb, Re[Sc[[1]]], Re[Sd], gauge, (1/2 fak[#1,#2,#3,#4,#6,#5,#7,#8])&];
					Quartic\[Lambda]abcd[sym, Sa, Sb, Im[Sc[[1]]], Im[Sd], gauge, (1/2 fak[#1,#2,#3,#4,#6,#5,#7,#8])&];
					Return[];
				];
				Quartic\[Lambda]abcd[sym, Sa, Sb, Re[Sc[[1]]], Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#6,#5,#7,#8])&];
				Quartic\[Lambda]abcd[sym, Sa, Sb, Im[Sc[[1]]], Sd, gauge, (-1/Sqrt[2] fak[#1,#2,#3,#4,#6,#5,#7,#8])&];
				Return[];
			];
			posC = ListPosition[ComplexScalarList, Sc];
			If[posC != {},
				posD = ListPosition[adj/@ComplexScalarList, Sd];
				If[posD != {} && posC == posD,
					Quartic\[Lambda]abcd[sym, Sa, Sb, Re[Sc], Re[Sd[[1]]], gauge, (1/2 fak[#1,#2,#3,#4,#5,#6,#8,#7])&];
					Quartic\[Lambda]abcd[sym, Sa, Sb, Im[Sc], Im[Sd[[1]]], gauge, (1/2 fak[#1,#2,#3,#4,#5,#6,#8,#7])&];
					Return[];
				];
				Quartic\[Lambda]abcd[sym, Sa, Sb, Re[Sc], Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Quartic\[Lambda]abcd[sym, Sa, Sb, Im[Sc], Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Return[];
			];
			posD = ListPosition[adj/@ComplexScalarList, Sd];
			If[posD != 0,
				Quartic\[Lambda]abcd[sym, Sa, Sb, Sc, Re[Sd[[1]]], gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#8,#7])&];
				Quartic\[Lambda]abcd[sym, Sa, Sb, Sc, Im[Sd[[1]]], gauge, (-1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#8,#7])&];
				Return[];
			];
			posD = ListPosition[ComplexScalarList, Sd];
			If[posD != 0,
				Quartic\[Lambda]abcd[sym, Sa, Sb, Sc, Re[Sd], gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Quartic\[Lambda]abcd[sym, Sa, Sb, Sc, Im[Sd], gauge, (1/Sqrt[2] fak[#1,#2,#3,#4,#5,#6,#7,#8])&];
				Return[];
			];
			posA = ListPosition[RealScalarList,_List?(#[[1]] == Sa &)];
			posB = ListPosition[RealScalarList,_List?(#[[1]] == Sb &)];
			posC = ListPosition[RealScalarList,_List?(#[[1]] == Sc &)];
			posD = ListPosition[RealScalarList,_List?(#[[1]] == Sd &)];
			If[posA == {} || posB == {} || posC == {} || posD == {},
				Message[Quartic::UnknownParticle];,
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
							Continue[];
						];
						iter++;
					];
				];
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
				ListQuarticSym = Append[ListQuarticSym, {sym, pa, pb, pc, pd, gauge, fak}];,
				ListQuarticSym[[pos, 7]] = Evaluate[ListQuarticSym[[pos, 7]][#1,#2,#3,#4,#5,#6,#7,#8] + fak[#1,#2,#3,#4,#5,#6,#7,#8]]&;
			];
		];
		
		(* Interfaces for Beta functions *)
		
		\[Beta][\[Alpha][sym_], loop_] := Module[
			{pos},
			pos = ListPosition[ListGauge,_List?(#[[1]] == sym &)];
			If[pos != {}, 
				Return[BetaGauge[pos[[1,1]], loop]];
			];
			Return[0];
		];
		
		\[Beta][sym_, loop_] := Module[
			{pos},
			pos = ListPosition[ListGauge,_List?(#[[1]] == sym &)];
			If[pos != {}, 
				Return[Expand[(\[Beta][\[Alpha][sym], loop] Sqr[4 Pi]/(2 sym))//.subAlpha]];
			];
		];
		
		\[Beta][SType_, FType1_, FType2_, SList_, FList1_, FList2_, loop_ ] := Module[
			{posS, posF1, posF2},
			If[MemberQ[ComplexScalarList, _?((# === SType)&)], 
				Return[Sqrt[2]\[Beta][Re[SType], FType1, FType2, SList, FList1, FList2, loop]];
			];
			posS  = ListPosition[RealScalarList,_List?(#[[1]] == SType &)];
			posF1 = ListPosition[WeylFermionList,_List?(#[[1]] == FType1 &)];
			posF2 = ListPosition[WeylFermionList,_List?(#[[1]] == FType2 &)];
			If[posS == {} || posF1 == {} || posF2 == {},
				Message[Yukawa::UnknownParticle];
				Return[];
			];
			Return[BetaYukawa[posS[[1,1]], posF1[[1,1]], posF2[[1,1]], SList, FList1, FList2, loop]];
		];
		
		\[Beta][SType1_, SType2_, SType3_, SType4_, SList1_, SList2_, SList3_, SList4_, loop_] := Module[
			{pos1, pos2, pos3, pos4},
			If[MemberQ[ComplexScalarList, _?((# === SType1)&)],
				Return[Sqrt[2] \[Beta][Re[SType1], SType2, SType3, SType4, SList1, SList2, SList3, SList4, loop]];
			];
			If[MemberQ[ComplexScalarList, _?((# === SType2)&)],
				Return[Sqrt[2] \[Beta][SType1, Re[SType2], SType3, SType4, SList1, SList2, SList3, SList4, loop]];
			];
			If[MemberQ[ComplexScalarList, _?((# === SType3)&)],
				Return[Sqrt[2] \[Beta][SType1, SType2, Re[SType3], SType4, SList1, SList2, SList3, SList4, loop]];
			];
			If[MemberQ[ComplexScalarList, _?((# === SType4)&)],
				Return[Sqrt[2] \[Beta][SType1, SType2, SType3, Re[SType4], SList1, SList2, SList3, SList4, loop]];
			];
			pos1  = ListPosition[RealScalarList,_List?(#[[1]] == SType1 &)];
			pos2  = ListPosition[RealScalarList,_List?(#[[1]] == SType2 &)];
			pos3  = ListPosition[RealScalarList,_List?(#[[1]] == SType3 &)];
			pos4  = ListPosition[RealScalarList,_List?(#[[1]] == SType4 &)];
			If[pos1 == {} || pos2 == {} || pos3 == {} || pos4 == {},
				Message[Quartic::UnknownParticle];
				Return[];
			];
			Return[BetaQuartic[pos1[[1,1]], pos2[[1,1]], pos3[[1,1]], pos4[[1,1]], SList1, SList2, SList3, SList4, loop]];
		];
		
		(* Backend for Beta functions *)
		
		BetaGauge[pos_, 0] := \[Alpha][ListGauge[[pos,1]]];
		
		BetaGauge[pos_, 1] := Module[
			{beta,x},
			beta = 0;
			beta = beta - 22/3 Sqr[\[Alpha][ListGauge[[pos,1]]]] C2[ListGauge[[pos,1]]]; 
			beta = beta + 4/3 Sqr[\[Alpha][ListGauge[[pos,1]]]] FSum[Hold[S2[WeylFermionList[[#,1]],ListGauge[[pos,1]]]]];
			beta = beta + 1/3 Sqr[\[Alpha][ListGauge[[pos,1]]]] SSum[Hold[S2[RealScalarList[[#,1]], ListGauge[[pos,1]]]]];
			Return[beta];
		];
		
		BetaGauge[pos_, 2] := Module[
			{beta,f,s},
			beta = 0;
			beta = beta - 2 Sqr[\[Alpha][ListGauge[[pos,1]]]] Y4[F,ListGauge[[pos, 1]]]/Sqr[4 Pi];
			beta = beta - 68/3 Power[\[Alpha][ListGauge[[pos,1]]], 3] Sqr[C2[ListGauge[[pos,1]]]];
			beta = beta + Sqr[\[Alpha][ListGauge[[pos,1]]]] FSum[Hold[(Sum[4 \[Alpha][ListGauge[[i,1]]] C2[WeylFermionList[[#,1]], ListGauge[[i,1]]],{i,1,NumberOfSubgroups}] + 20/3 \[Alpha][ListGauge[[pos,1]]] C2[ListGauge[[pos,1]]])S2[WeylFermionList[[#,1]], ListGauge[[pos,1]]]]];
			beta = beta + Sqr[\[Alpha][ListGauge[[pos,1]]]] SSum[Hold[(Sum[4 \[Alpha][ListGauge[[i,1]]] C2[RealScalarList[[#,1]], ListGauge[[i,1]]],{i,1,NumberOfSubgroups}] + 2/3 \[Alpha][ListGauge[[pos,1]]] C2[ListGauge[[pos,1]]])S2[RealScalarList[[#,1]], ListGauge[[pos,1]]]]];
			Return[beta];
		];
		
		BetaYukawa[pa_, pi_, pj_, la_, li_, lj_, 0] := ReleaseHold[Yuk[pa][pi,pj] /. subYuk]/.{
			adj[Yukawa[a_]]:>(If[(MatchQ[ListYukawa[[a,6]], Mat[___]] || MatchQ[ListYukawa[[a,6]], Conjugate[Mat[___]]] || MatchQ[ListYukawa[[a,6]], aa_ Mat[___]] || MatchQ[ListYukawa[[a,6]], aa_ Conjugate[Mat[___]]]  || MatchQ[ListYukawa[[a,6]], Mat[___]&] || MatchQ[ListYukawa[[a,6]], Conjugate[Mat[___]]&]  || MatchQ[ListYukawa[[a,6]], aa_ Mat[___]&] || MatchQ[ListYukawa[[a,6]], aa_ Conjugate[Mat[___]]&]), adj[ListYukawa[[a, 1]]][lj[[1]], li[[1]]], adj[ListYukawa[[a, 1]]]] Refine[Conjugate[ListYukawa[[a,6]][la[[1]], la[[2]], lj[[1]], li[[1]]]/.{Mat:>Identity}]] Times@@(Function[{x}, Refine[Conjugate[ListYukawa[[a,5,x]][la[[2+x]], lj[[1+x]], li[[1+x]]]]]]/@Range[NumberOfSubgroups])),
			Yukawa[a_]:>(If[(MatchQ[ListYukawa[[a,6]], Mat[___]] || MatchQ[ListYukawa[[a,6]], Conjugate[Mat[___]]] || MatchQ[ListYukawa[[a,6]], aa_ Mat[___]] || MatchQ[ListYukawa[[a,6]], aa_ Conjugate[Mat[___]]]  || MatchQ[ListYukawa[[a,6]], Mat[___]&] || MatchQ[ListYukawa[[a,6]], Conjugate[Mat[___]]&]  || MatchQ[ListYukawa[[a,6]], aa_ Mat[___]&] || MatchQ[ListYukawa[[a,6]], aa_ Conjugate[Mat[___]]&]), ListYukawa[[a, 1]][li[[1]], lj[[1]]], ListYukawa[[a, 1]]] (ListYukawa[[a,6]][la[[1]], la[[2]], li[[1]], lj[[1]]]/.{Mat:>Identity}) Times@@(Function[{x}, ListYukawa[[a,5,x]][la[[2+x]], li[[1+x]], lj[[1+x]]]]/@Range[NumberOfSubgroups]))
		};
		
		BetaYukawa[pa_, pi_, pj_, la_, li_, lj_, 1] := Module[
			{beta, ss, ss1, ii, x, x2, x3, sumIdx},
			beta = 0;
			beta += 1/2 Sum[
				Sum@@Join[
					{
						SolveProd3Fast[Yuk[ss1[0]], adj[Yuk[ss1[0]]], Yuk[pa], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss1[2+x2], ss1[2+x2], la[[2+x2]]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], ss1[1], ss1[2], la[[1]], la[[2]]}]],
						{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
						{ss1[2], 1, RealScalarList[[ss1[0],2,1]]}
					},
					Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
				],
				{ss1[0], 1, SNumber[]}
			];
			beta += 1/2 Sum[
				Sum@@Join[
					{
						SolveProd3Fast[Yuk[pa], adj[Yuk[ss1[0]]], Yuk[ss1[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {la[[2+x2]], ss1[2+x2], ss1[2+x2]}]/@Range[NumberOfSubgroups], {la[[1]], la[[2]], ss1[1], ss1[2], ss1[1], ss1[2]}]],
						{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
						{ss1[2], 1, RealScalarList[[ss1[0],2,1]]}
					},
					Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
				],
				{ss1[0], 1, SNumber[]}
			];
			beta += 2 Sum[
				Sum@@Join[
					{
						SolveProd3Fast[Yuk[ss1[0]], adj[Yuk[pa]], Yuk[ss1[0]], Prepend[li,pi], Prepend[lj,pj], Prepend[Function[{x2}, {ss1[2+x2], la[[2+x2]], ss1[2+x2]}]/@Range[NumberOfSubgroups], {ss1[1], ss1[2], la[[1]], la[[2]], ss1[1], ss1[2]}]],
						{ss1[1], 1, RealScalarList[[ss1[0],2,1]]},
						{ss1[2], 1, RealScalarList[[ss1[0],2,1]]}
					},
					Function[{x}, {ss1[2+x], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups]
				],
				{ss1[0], 1, SNumber[]}
			];
			beta = beta + 1/2 Sum[
				Sum@@Join[
					{
						(
							SolveTrace2Fast[Yuk[pa], adj[Yuk[sumIdx[0]]], Prepend[Function[{x}, {la[[2+x]], sumIdx[2+x]}]/@Range[NumberOfSubgroups], {la[[1]], la[[2]], sumIdx[1], sumIdx[2]}]] +
							SolveTrace2Fast[adj[Yuk[pa]], Yuk[sumIdx[0]], Prepend[Function[{x}, {la[[2+x]], sumIdx[2+x]}]/@Range[NumberOfSubgroups], {la[[1]], la[[2]], sumIdx[1], sumIdx[2]}]]
						) BetaYukawa[sumIdx[0], pi, pj, sumIdx/@Range[NumberOfSubgroups+2], li, lj, 0],
						{sumIdx[1], 1, RealScalarList[[sumIdx[0], 2, 1]]}, 
						{sumIdx[2], 1, RealScalarList[[sumIdx[0], 2, 2]]}
					}, Function[{x}, {sumIdx[x+2], 1, SMultiplicity[sumIdx[0], x]}]/@Range[NumberOfSubgroups]
				],
				{sumIdx[0], 1, SNumber[]}
			]/.{tr[adj[a_],b_]:>tr[b,adj[a]]};
			beta -= 3 Sum[Sqr[ListGauge[[ii,1]]](C2[WeylFermionList[[pi,1]], ListGauge[[ii,1]]] + C2[WeylFermionList[[pj,1]], ListGauge[[ii,1]]]) BetaYukawa[pa, pi, pj, la, li, lj, 0], {ii, 1, NumberOfSubgroups}];
			Return[beta/Sqr[4\[Pi]]];
		];
		
		BetaYukawa[pa_, pi_, pj_, la_, li_, lj_, 2] := Module[
			{beta, ssb, ssc, ss, ss2, ss3, ff, ii, ii2, x},
			beta = 0;
			beta += 2 Sum[YukawaProd[Yuk[ssc], adj[Yuk[ssb]], Yuk[pa], adj[Yuk[ssc]], Yuk[ssb], pi, pj, li, lj, Join[{KroneckerDelta[#1,#7] KroneckerDelta[#2,#8] KroneckerDelta[#3,#9] KroneckerDelta[#4,#10] KroneckerDelta[#5,la[[1]]] KroneckerDelta[#6,la[[2]]] &}, Function[{x}, KroneckerDelta[#1, #4] KroneckerDelta[#2,#5] KroneckerDelta[#3, la[[x+2]]] &]/@Range[NumberOfSubgroups]]], {ssb, 1, SNumber[]}, {ssc, 1, SNumber[]}];
			beta -= 2 Sum[YukawaProd[Yuk[ssc], adj[Yuk[ssb]], Yuk[pa], adj[Yuk[ssb]], Yuk[ssc], pi, pj, li, lj, Join[{KroneckerDelta[#1,#9] KroneckerDelta[#2,#10] KroneckerDelta[#3,#7] KroneckerDelta[#4,#8] KroneckerDelta[#5,la[[1]]] KroneckerDelta[#6,la[[2]]] &}, Function[{x}, KroneckerDelta[#1, #5] KroneckerDelta[#2,#4] KroneckerDelta[#3, la[[x+2]]] &]/@Range[NumberOfSubgroups]]], {ssb, 1, SNumber[]}, {ssc, 1, SNumber[]}];
			beta -= Sum[YukawaProd[Yuk[ssb], adj[Yuk[ssc]], Yuk[ssc], adj[Yuk[pa]], Yuk[ssb], pi, pj, li, lj, Join[{KroneckerDelta[#1,#9] KroneckerDelta[#2,#10] KroneckerDelta[#3,#5] KroneckerDelta[#4,#6] KroneckerDelta[#7,la[[1]]] KroneckerDelta[#8,la[[2]]] &}, Function[{x}, KroneckerDelta[#1, #5] KroneckerDelta[#2, #3] KroneckerDelta[#4, la[[x+2]]] &]/@Range[NumberOfSubgroups]]], {ssb, 1, SNumber[]}, {ssc, 1, SNumber[]}];
			beta -= Sum[YukawaProd[Yuk[ssb], adj[Yuk[pa]], Yuk[ssc], adj[Yuk[ssc]], Yuk[ssb], pi, pj, li, lj, Join[{KroneckerDelta[#1,#9] KroneckerDelta[#2,#10] KroneckerDelta[#3,la[[1]]] KroneckerDelta[#4,la[[2]]] KroneckerDelta[#5,#7] KroneckerDelta[#6,#8] &}, Function[{x}, KroneckerDelta[#1, #5] KroneckerDelta[#3, #4] KroneckerDelta[#2, la[[x+2]]] &]/@Range[NumberOfSubgroups]]], {ssb, 1, SNumber[]}, {ssc, 1, SNumber[]}];
			beta -= 1/8 Sum[YukawaProd[Yuk[ssb], adj[Yuk[ssc]], Yuk[ssc], adj[Yuk[ssb]], Yuk[pa], pi, pj, li, lj, Join[{KroneckerDelta[#1,#7] KroneckerDelta[#2,#8] KroneckerDelta[#3,#5] KroneckerDelta[#4,#6] KroneckerDelta[#9,la[[1]]] KroneckerDelta[#10,la[[2]]] &}, Function[{x}, KroneckerDelta[#1, #4] KroneckerDelta[#2, #3] KroneckerDelta[#5, la[[x+2]]] &]/@Range[NumberOfSubgroups]]], {ssb, 1, SNumber[]}, {ssc, 1, SNumber[]}];
			beta -= 1/8 Sum[YukawaProd[Yuk[pa], adj[Yuk[ssb]], Yuk[ssc], adj[Yuk[ssc]], Yuk[ssb], pi, pj, li, lj, Join[{KroneckerDelta[#1,la[[1]]] KroneckerDelta[#2,la[[2]]] KroneckerDelta[#3,#9] KroneckerDelta[#4,#10] KroneckerDelta[#5,#7] KroneckerDelta[#6,#8] &}, Function[{x}, KroneckerDelta[#2, #5] KroneckerDelta[#3, #4] KroneckerDelta[#1, la[[x+2]]] &]/@Range[NumberOfSubgroups]]], {ssb, 1, SNumber[]}, {ssc, 1, SNumber[]}];
			beta -= 2 Sum[Sum@@Join[
				{
					(Y2S[Prepend[la, pa], ss/@Range[0, NumberOfSubgroups+2]]//.subScalarInvariants) YukawaProd[Yuk[ssb], adj[Yuk[ss[0]]], Yuk[ssb], pi, pj, li, lj, Join[{KroneckerDelta[#1,#5] KroneckerDelta[#2,#6] KroneckerDelta[#3,ss[1]] KroneckerDelta[#4,ss[2]] &}, Function[{x}, KroneckerDelta[#1, #3] KroneckerDelta[#2, ss[x+2]] &]/@Range[NumberOfSubgroups]]],
					{ss[1], 1, RealScalarList[[ss[0], 2,1]]},
					{ss[2], 1, RealScalarList[[ss[0], 2,2]]}
				},
				Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups]
			], {ss[0], 1, SNumber[]}, {ssb, 1, SNumber[]}];
			beta -= Sum[Sum@@Join[
				{
					(( Hbar2S[Prepend[la, pa], ss/@Range[0, NumberOfSubgroups+2]] + 3/2 H2S[Prepend[la, pa], ss/@Range[0, NumberOfSubgroups+2]] - 1/2 \[CapitalLambda]2S[Prepend[la, pa], ss/@Range[0, NumberOfSubgroups+2]])//.subScalarInvariants) BetaYukawa[ss[0], pi, pj, ss/@Range[NumberOfSubgroups+2], li, lj, 0],
					{ss[1], 1, RealScalarList[[ss[0], 2,1]]},
					{ss[2], 1, RealScalarList[[ss[0], 2,2]]}
				},
				Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups]
			], {ss[0], 1, SNumber[]}];
			beta -= 3/4 Sum[Sum@@Join[
				{
					(Y2S[ss/@Range[0, NumberOfSubgroups+2], ss2/@Range[0, NumberOfSubgroups+2]]//.subScalarInvariants) (YukawaProd[Yuk[ss[0]], adj[Yuk[ss2[0]]], Yuk[pa], pi, pj, li, lj, Join[{KroneckerDelta[#1, ss[1]] KroneckerDelta[#2,ss[2]] KroneckerDelta[#3,ss2[1]] KroneckerDelta[#4,ss2[2]] KroneckerDelta[#5,la[[1]]] KroneckerDelta[#6,la[[2]]] &}, Function[{x}, KroneckerDelta[#1, ss[x+2]] KroneckerDelta[#2, ss2[x+2]] KroneckerDelta[#3, la[[x+2]]] &]/@Range[NumberOfSubgroups]]] + YukawaProd[Yuk[pa], adj[Yuk[ss2[0]]], Yuk[ss[0]], pi, pj, li, lj, Join[{KroneckerDelta[#1,la[[1]]] KroneckerDelta[#2,la[[2]]] KroneckerDelta[#3,ss2[1]] KroneckerDelta[#4,ss2[2]] KroneckerDelta[#5,ss[1]] KroneckerDelta[#6,ss[2]] &}, Function[{x}, KroneckerDelta[#3, ss[x+2]] KroneckerDelta[#2, ss2[x+2]] KroneckerDelta[#1, la[[x+2]]] &]/@Range[NumberOfSubgroups]]]),
					{ss[1], 1, RealScalarList[[ss[0], 2,1]]},
					{ss[2], 1, RealScalarList[[ss[0], 2,2]]},
					{ss2[1], 1, RealScalarList[[ss2[0], 2,1]]},
					{ss2[2], 1, RealScalarList[[ss2[0], 2,2]]}
				},
				Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups],
				Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
			], {ss[0], 1, SNumber[]}, {ss2[0], 1, SNumber[]}];
			beta -= 2 Sum[Sum@@Join[
				{
					24 BetaQuartic[pa, ss[0], ss2[0], ss3[0], la, ss/@Range[NumberOfSubgroups+2], ss2/@Range[NumberOfSubgroups+2], ss3/@Range[NumberOfSubgroups+2],0] YukawaProd[Yuk[ss[0]], adj[Yuk[ss2[0]]], Yuk[ss3[0]], pi, pj, li, lj, Join[{KroneckerDelta[#1,ss[1]] KroneckerDelta[#2,ss[2]] KroneckerDelta[#3,ss2[1]] KroneckerDelta[#4,ss2[2]] KroneckerDelta[#5,ss3[1]] KroneckerDelta[#6,ss3[2]] &}, Function[{x}, KroneckerDelta[#1, ss[x+2]] KroneckerDelta[#2, ss2[x+2]] KroneckerDelta[#3, ss3[x+2]] &]/@Range[NumberOfSubgroups]]],
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
			], {ss[0], 1, SNumber[]}, {ss2[0], 1, SNumber[]}, {ss3[0], 1, SNumber[]}];
			beta += Sum[
				Sqr[ListGauge[[ii,1]]](
					3 YukawaProd[C2[F, ii], Yuk[ssb], adj[Yuk[pa]], Yuk[ssb], pi, pj, li, lj, Join[{KroneckerDelta[#3,#7] KroneckerDelta[#4,#8] KroneckerDelta[#5,la[[1]]] KroneckerDelta[#6,la[[2]]] &}, Function[{x}, KroneckerDelta[#1, 1] KroneckerDelta[#2, #4] KroneckerDelta[#3, la[[x+2]]] &]/@Range[NumberOfSubgroups]]]  +
					3 YukawaProd[Yuk[ssb], adj[Yuk[pa]], Yuk[ssb], C2[F, ii], pi, pj, li, lj, Join[{KroneckerDelta[#1,#5] KroneckerDelta[#2,#6] KroneckerDelta[#3,la[[1]]] KroneckerDelta[#4,la[[2]]] &}, Function[{x}, KroneckerDelta[#4, 1] KroneckerDelta[#1, #3] KroneckerDelta[#2, la[[x+2]]] &]/@Range[NumberOfSubgroups]]]  +
					5 YukawaProd[Yuk[ssb], C2[F, ii], adj[Yuk[pa]], Yuk[ssb], pi, pj, li, lj, Join[{KroneckerDelta[#1,#7] KroneckerDelta[#2,#8] KroneckerDelta[#5,la[[1]]] KroneckerDelta[#6,la[[2]]] &}, Function[{x}, KroneckerDelta[#2, 1] KroneckerDelta[#1, #4] KroneckerDelta[#3, la[[x+2]]] &]/@Range[NumberOfSubgroups]]] +
					5 YukawaProd[Yuk[ssb], adj[Yuk[pa]], C2[F, ii],  Yuk[ssb], pi, pj, li, lj, Join[{KroneckerDelta[#1,#7] KroneckerDelta[#2,#8] KroneckerDelta[#3,la[[1]]] KroneckerDelta[#4,la[[2]]] &}, Function[{x}, KroneckerDelta[#3, 1] KroneckerDelta[#1, #4] KroneckerDelta[#2, la[[x+2]]] &]/@Range[NumberOfSubgroups]]] - 
					7/4 YukawaProd[C2[F, ii], Yuk[ssb], adj[Yuk[ssb]], Yuk[pa], pi, pj, li, lj, Join[{KroneckerDelta[#3,#5] KroneckerDelta[#4,#6] KroneckerDelta[#7,la[[1]]] KroneckerDelta[#8,la[[2]]] &}, Function[{x}, KroneckerDelta[#1, 1] KroneckerDelta[#2, #3] KroneckerDelta[#4, la[[x+2]]] &]/@Range[NumberOfSubgroups]]] -
					7/4 YukawaProd[Yuk[pa], adj[Yuk[ssb]], Yuk[ssb], C2[F, ii], pi, pj, li, lj, Join[{KroneckerDelta[#3,#5] KroneckerDelta[#4,#6] KroneckerDelta[#1,la[[1]]] KroneckerDelta[#2,la[[2]]] &}, Function[{x}, KroneckerDelta[#4, 1] KroneckerDelta[#2, #3] KroneckerDelta[#1, la[[x+2]]] &]/@Range[NumberOfSubgroups]]] -
					1/4 YukawaProd[Yuk[ssb], C2[F, ii], adj[Yuk[ssb]], Yuk[pa], pi, pj, li, lj, Join[{KroneckerDelta[#1,#5] KroneckerDelta[#2,#6] KroneckerDelta[#7,la[[1]]] KroneckerDelta[#8,la[[2]]] &}, Function[{x}, KroneckerDelta[#2, 1] KroneckerDelta[#1, #3] KroneckerDelta[#4, la[[x+2]]] &]/@Range[NumberOfSubgroups]]] -
					1/4 YukawaProd[Yuk[pa], adj[Yuk[ssb]], C2[F, ii], Yuk[ssb], pi, pj, li, lj, Join[{KroneckerDelta[#1,la[[1]]] KroneckerDelta[#2,la[[2]]] KroneckerDelta[#3,#7] KroneckerDelta[#4,#8] &}, Function[{x}, KroneckerDelta[#3, 1] KroneckerDelta[#2, #4] KroneckerDelta[#1, la[[x+2]]] &]/@Range[NumberOfSubgroups]]]
				),
				{ssb, 1, SNumber[]},
				{ii, 1, NumberOfSubgroups}
			]/.{prod[a___, C2[b___], c___][d___]:>C2[b] prod[a,c][d]};
			beta += Sum[ 6 Sqr[ListGauge[[ii,1]]] H2t[ii, Prepend[la, pa], Prepend[li, pi], Prepend[lj, pj]] //.subScalarInvariants, {ii, 1, NumberOfSubgroups}];
			beta += Sum[
				5 Sqr[ListGauge[[ii,1]]] Sum@@Join[
					{
						BetaYukawa[ss[0], pi, pj, ss/@Range[NumberOfSubgroups+2], li, lj, 0] Y2FS[ii, Prepend[la, pa], ss/@Range[0,NumberOfSubgroups+2]] //.subScalarInvariants,
						{ss[1], 1, RealScalarList[[ss[0], 2,1]]},
						{ss[2], 1, RealScalarList[[ss[0], 2,2]]}
					},
					Function[{x}, {ss[x+2], 1, SMultiplicity[ss[0], x]}]/@Range[NumberOfSubgroups]
				],
				{ss[0], 1, SNumber[]},
				{ii, 1, NumberOfSubgroups}
			];
			beta += Sum[
				Sqr[ListGauge[[ii,1]]] (
					(6 C2[RealScalarList[[ssb,1]], ListGauge[[ii,1]]] - 12 C2[RealScalarList[[pa,1]], ListGauge[[ii,1]]]) YukawaProd[Yuk[ssb], adj[Yuk[pa]], Yuk[ssb], pi, pj, li, lj, Join[{KroneckerDelta[#1,#5] KroneckerDelta[#2,#6] KroneckerDelta[#3,la[[1]]] KroneckerDelta[#4,la[[2]]] &}, Function[{x}, KroneckerDelta[#1, #3] KroneckerDelta[#2, la[[x+2]]] &]/@Range[NumberOfSubgroups]]] +
					9/2 C2[RealScalarList[[ssb,1]], ListGauge[[ii,1]]] (YukawaProd[Yuk[ssb], adj[Yuk[ssb]], Yuk[pa], pi, pj, li, lj, Join[{KroneckerDelta[#1,#3] KroneckerDelta[#2,#4] KroneckerDelta[#5,la[[1]]] KroneckerDelta[#6,la[[2]]] &}, Function[{x}, KroneckerDelta[#1, #2] KroneckerDelta[#3, la[[x+2]]] &]/@Range[NumberOfSubgroups]]] + YukawaProd[Yuk[pa], adj[Yuk[ssb]], Yuk[ssb], pi, pj, li, lj, Join[{KroneckerDelta[#1,la[[1]]] KroneckerDelta[#2,la[[2]]] KroneckerDelta[#3,#5] KroneckerDelta[#4,#6] &}, Function[{x}, KroneckerDelta[#2, #3] KroneckerDelta[#1, la[[x+2]]] &]/@Range[NumberOfSubgroups]]])
				),
				{ssb, 1, SNumber[]},
				{ii, 1, NumberOfSubgroups}
			];
			beta -= 3/2 Sum[
				Sqr[ListGauge[[ii,1]] ListGauge[[ii2,1]]] BetaYukawa[pa, pi, pj, la, li, lj, 0] (C2[WeylFermionList[[pi,1]], ListGauge[[ii,1]]] C2[WeylFermionList[[pi,1]], ListGauge[[ii2,1]]] + C2[WeylFermionList[[pj,1]], ListGauge[[ii,1]]] C2[WeylFermionList[[pj,1]], ListGauge[[ii2,1]]]),
				{ii, 1, NumberOfSubgroups},
				{ii2, 1, NumberOfSubgroups}
			];
			beta += 6 Sum[
				Sqr[ListGauge[[ii, 1]] ListGauge[[ii2, 1]]] C2[RealScalarList[[pa,1]], ListGauge[[ii,1]]] BetaYukawa[pa, pi, pj, la, li, lj, 0] (C2[WeylFermionList[[pi,1]], ListGauge[[ii2,1]]] + C2[WeylFermionList[[pj,1]], ListGauge[[ii2,1]]]),
				{ii, 1, NumberOfSubgroups},
				{ii2, 1, NumberOfSubgroups}
			];
			beta += Sum[
				Power[ListGauge[[ii,1]],4](
					-97/6 C2[ListGauge[[ii,1]]] + 
					5/3 Sum[S2[WeylFermionList[[ff,1]], ListGauge[[ii,1]]], {ff, 1, FNumber[]}] + 
					11/12 Sum[S2[RealScalarList[[ssb,1]], ListGauge[[ii,1]]], {ssb, 1, SNumber[]}]
				) BetaYukawa[pa, pi, pj, la, li, lj, 0] (C2[WeylFermionList[[pi,1]], ListGauge[[ii, 1]]] + C2[WeylFermionList[[pj,1]], ListGauge[[ii, 1]]]),
				{ii, 1, NumberOfSubgroups}
			];
			beta -= 21/2 Sum[
				Sqr[ListGauge[[ii,1]] ListGauge[[ii2,1]]] C2[RealScalarList[[pa,1]], ListGauge[[ii,1]]] C2[RealScalarList[[pa,1]], ListGauge[[ii2,1]]] BetaYukawa[pa, pi, pj, la, li, lj, 0], 
				{ii, 1, NumberOfSubgroups}, 
				{ii2, 1, NumberOfSubgroups}
			];
			beta += Sum[
				Power[ListGauge[[ii,1]],4](
					49/4 C2[ListGauge[[ii,1]]] -
					1/4 Sum[S2[RealScalarList[[ssb,1]], ListGauge[[ii,1]]], {ssb, 1, SNumber[]}] -
					Sum[S2[WeylFermionList[[ff, 1]], ListGauge[[ii,1]]] ,{ff, 1, FNumber[]}]
				) C2[RealScalarList[[pa,1]], ListGauge[[ii,1]]] BetaYukawa[pa, pi, pj, la, li, lj, 0],
				{ii, 1, NumberOfSubgroups}
			];
			Return[beta/Power[4\[Pi], 4]];
		];
		
		
		BetaQuartic[a_, b_, c_, d_, la_, lb_, lc_, ld_, 0] := Module[
			{pa, pb, pc, pd, q},
			Return[
				ReleaseHold[(Quartic[a,b,c,d]/.subQuart)]//.{
				Quart[q_]:>((ListQuarticSym[[q,1]] ListQuarticSym[[q,7]][la[[1]], la[[2]], lb[[1]], lb[[2]], lc[[1]], lc[[2]], ld[[1]], ld[[2]]])(Times@@(Function[{x},ListQuarticSym[[q,6,x]][la[[2+x]], lb[[2+x]], lc[[2+x]], ld[[2+x]]]]/@Range[NumberOfSubgroups])))}
			];
		];
		
		
		BetaQuartic[pa_, pb_, pc_, pd_, la_, lb_, lc_, ld_, 1] := Module[
			{beta, ss, ii, x, ii2},
			beta = 0;
			beta = beta + Sqr[24]/8 Perm[\[CapitalLambda]2[Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]]]//.subScalarInvariants;
			beta = beta - Perm[H[Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]]]//.subScalarInvariants//.{tr[adj[a_], b_, adj[c_], d_]:>tr[b, adj[c], d, adj[a]]};
			beta = beta + 24 \[CapitalLambda]Y[Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]]//.subScalarInvariants//.{tr[adj[a_], b_]:>tr[b, adj[a]]};
			beta = beta - 3*24 Sum[Sqr[ListGauge[[ii,1]]]\[CapitalLambda]S[ii][Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]], {ii, 1, NumberOfSubgroups}]//.subScalarInvariants;
			beta = beta + 3/4 Sum[Sqr[ListGauge[[ii,1]]] Sqr[ListGauge[[ii2,1]]] Perm[As[ii,ii2][Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]]], {ii, 1, NumberOfSubgroups}, {ii2, 1, NumberOfSubgroups}]//.subScalarInvariants;
			Return[beta/(24 Sqr[4\[Pi]])];
		]
		
		BetaQuartic[pa_, pb_, pc_, pd_, la_, lb_, lc_, ld_, 2] := Module[
			{beta, ss1, ss2, sIdx ff, ii, ii2, ii3, x},
			beta = 0;
			beta += 12 BetaQuartic[pa, pb, pc, pd, la, lb, lc, ld, 0] (\[CapitalLambda]2S[Prepend[la,pa], Prepend[la,pa]] + \[CapitalLambda]2S[Prepend[lb,pb], Prepend[lb,pb]] + \[CapitalLambda]2S[Prepend[lc,pc], Prepend[lc,pc]]+ \[CapitalLambda]2S[Prepend[ld,pd], Prepend[ld,pd]])//.subScalarInvariants;
			beta -= 6 Sqr[24] Perm[\[CapitalLambda]bar3[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]] //.subScalarInvariants;
			beta -= 6*24 Perm[\[CapitalLambda]bar2Y[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]]//.subScalarInvariants;
			beta += 12 Perm[Hbar\[Lambda][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]]//.subScalarInvariants;
			beta -= 12 BetaQuartic[pa, pb, pc, pd, la, lb, lc, ld, 0] 
				(
					3 H2S[Prepend[la, pa], Prepend[la, pa]] + 2 Hbar2S[Prepend[la, pa], Prepend[la, pa]] + 
					3 H2S[Prepend[lb, pb], Prepend[lb, pb]] + 2 Hbar2S[Prepend[lb, pb], Prepend[lb, pb]] +
					3 H2S[Prepend[lc, pc], Prepend[lc, pc]] + 2 Hbar2S[Prepend[lc, pc], Prepend[lc, pc]] +
					3 H2S[Prepend[ld, pd], Prepend[ld, pd]] + 2 Hbar2S[Prepend[ld, pd], Prepend[la, pd]]
				)//.subScalarInvariants;
			beta += 2(Perm[HY[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]] +  Perm[HbarY[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]] +  Perm[H3[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]]) //.subScalarInvariants;
			beta += Sum[
				Sqr[ListGauge[[ii,1]]](
					24*6 Perm[\[CapitalLambda]bar2S[ii][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]] - 24*18 Perm[\[CapitalLambda]2g[ii][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]] - 2 Perm[HF[ii][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]] + 1/2 (C2[RealScalarList[[pa, 1]] , ListGauge[[ii,1]]] + C2[RealScalarList[[pb, 1]] , ListGauge[[ii,1]]] + C2[RealScalarList[[pc, 1]] , ListGauge[[ii,1]]] + C2[RealScalarList[[pd, 1]] , ListGauge[[ii,1]]]) Perm[H[Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]] + 5*24 BetaQuartic[pa, pb, pc, pd, la, lb, lc, ld, 0] (
						Y2FS[ii, Prepend[la, pa], Prepend[la,pa]] + Y2FS[ii, Prepend[lb, pb], Prepend[lb,pb]] + Y2FS[ii, Prepend[lc, pc], Prepend[lc,pc]] + Y2FS[ii, Prepend[ld, pd], Prepend[ld,pd]]
					)
				)//.subScalarInvariants,
				{ii, 1, NumberOfSubgroups}
			];
			beta -= Sum[ 
				Power[ListGauge[[ii,1]],4] (
					(35/3 C2[ListGauge[[ii,1]]] - 5/3 Sum[S2[WeylFermionList[[ff,1]], ListGauge[[ii,1]]], {ff, 1, FNumber[]}] - 11/12 Sum[S2[RealScalarList[[ss1[0],1]], ListGauge[[ii,1]]], {ss1[0], 1, SNumber[]}])*24*\[CapitalLambda]S[ii][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]
				)//.subScalarInvariants,
				{ii, 1, NumberOfSubgroups}
			];
			beta += Sum[
				Sqr[ListGauge[[ii,1]] ListGauge[[ii2,1]]] (
					15 Perm[A\[Lambda][ii,ii2][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]] +
					3 Perm[Abar\[Lambda][ii,ii2][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]]  + 36 BetaQuartic[pa, pb, pc, pd, la, lb, lc, ld, 0] (
						C2[RealScalarList[[pa,1]], ListGauge[[ii,1]]] C2[RealScalarList[[pa,1]], ListGauge[[ii2,1]]] + 
						C2[RealScalarList[[pb,1]], ListGauge[[ii,1]]] C2[RealScalarList[[pb,1]], ListGauge[[ii2,1]]] +
						C2[RealScalarList[[pc,1]], ListGauge[[ii,1]]] C2[RealScalarList[[pc,1]], ListGauge[[ii2,1]]] +
						C2[RealScalarList[[pd,1]], ListGauge[[ii,1]]] C2[RealScalarList[[pd,1]], ListGauge[[ii2,1]]] 
					) - 1/2 Perm[BY[ii,ii2][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]] + 5 Perm[BbarY[ii,ii2][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]]
				)//.subScalarInvariants,
				{ii, 1, NumberOfSubgroups},
				{ii2, 1, NumberOfSubgroups}
			];
			beta += Sum[
				1/4 Perm[As[ii,ii2][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]](
					Sqr[ListGauge[[ii2,1]]] Power[ListGauge[[ii,1]],4] (
						161/6 C2[ListGauge[[ii,1]]] -
						16/3 Sum[S2[WeylFermionList[[ff,1]], ListGauge[[ii,1]]], {ff, 1, FNumber[]}] -
						7/3 Sum[S2[RealScalarList[[ss1[0],1]], ListGauge[[ii,1]]], {ss1[0], 1, SNumber[]}]
					) - 15/2 Sum[Sqr[ListGauge[[ii,1]] ListGauge[[ii2,1]] ListGauge[[ii3,1]]]( C2[RealScalarList[[pa,1]], ListGauge[[ii3,1]]] + C2[RealScalarList[[pb,1]], ListGauge[[ii3,1]]] + C2[RealScalarList[[pc,1]], ListGauge[[ii3,1]]] + C2[RealScalarList[[pd,1]], ListGauge[[ii3,1]]]), {ii3, 1, NumberOfSubgroups}]
				)//.subScalarInvariants,
				{ii, 1, NumberOfSubgroups},
				{ii2, 1, NumberOfSubgroups}
			];
			beta += 27/2 Sum[ Power[ListGauge[[ii,1]], 6] Perm[Ag[ii][Prepend[la, pa], Prepend[lb, pb], Prepend[lc, pc], Prepend[ld, pd]]], {ii, 1, NumberOfSubgroups}]//.subScalarInvariants;
			Return[beta/(24 Power[4 \[Pi], 4])];
		];
		
		
		(* Definition of Invariants *)
		ComputeInvariants[] := Module[
			{i, f, s, sIdx},
			subInvariants = {};
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
						If[ListGauge[[i,2]] === SU && ListGauge[[i,4,i]]==Sqr[ListGauge[[i,3]]]-1,
							subInvariants = Append[subInvariants, d[ListGauge[[i,1]]]->ListGauge[[i,4,i]]];
							subInvariants = Append[subInvariants, C2[ListGauge[[i,1]]]->ListGauge[[i,3]]];
						];
						(* Adjoint Rep in SO(N)*)
						If[ListGauge[[i,2]] === SO && ListGauge[[i,4,i]]==1/2 ListGauge[[i,3]](ListGauge[[i,3]]-1),
							subInvariants = Append[subInvariants, d[ListGauge[[i,1]]]->ListGauge[[i,4,i]]];
							subInvariants = Append[subInvariants, C2[ListGauge[[i,1]]]->(2 ListGauge[[i,3]] - 4)];
						];
					];
				];
				(* Fermion Invariants *)
				If[WeylFermionList != {},
					For[f=1, f<=FNumber[], f++,
						(* SU(N) subgroup *)
						If[ListGauge[[i,2]] === SU,
							If[WeylFermionList[[f,3,i]] === 1,
								subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 0];
								Continue[];,
								(* Fundamental Representation *)
								If[WeylFermionList[[f,3,i]] == ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 (Sqr[WeylFermionList[[f,3,i]]]-1)/WeylFermionList[[f,3,i]]];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 FMultiplicity[f]/WeylFermionList[[f,3,i]]];
								];
								(* Adjoint Representation *)
								If[WeylFermionList[[f,3,i]] == Sqr[ListGauge[[i,3]]] - 1,
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> FMultiplicity[f]/WeylFermionList[[f,3,i]] ListGauge[[i,3]]];
								];
								(* Symmetric Representation *)
								If[WeylFermionList[[f,3,i]] == 1/2 ListGauge[[i,3]] (ListGauge[[i,3]] + 1),
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> (ListGauge[[i,3]] + 2)(ListGauge[[i,3]] - 1)/ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> FMultiplicity[f]/WeylFermionList[[f,3,i]] (1/2 ListGauge[[i,3]] + 1)];
								];
								(* Anitsymmetric Representation *)
								If[WeylFermionList[[f,3,i]] == 1/2 ListGauge[[i,3]] (ListGauge[[i,3]] - 1),
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
								If[WeylFermionList[[f,3,i]] == ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> (ListGauge[[i,3]] - 1)];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 2 FMultiplicity[f]/WeylFermionList[[f,3,i]]];
								];
								(* Adjoint Representation *)
								If[WeylFermionList[[f,3,i]] == 1/2 ListGauge[[i,3]](ListGauge[[i,3]] - 1),
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> (2 ListGauge[[i,3]] - 4)];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> (2 ListGauge[[i,3]] - 4) FMultiplicity[f]/WeylFermionList[[f,3,i]]];
								];
								(* Symmetric Representation *)
								If[WeylFermionList[[f,3,i]] == 1/2 ListGauge[[i,3]](ListGauge[[i,3]] + 1) - 1,
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 2(ListGauge[[i,3]] + 2) FMultiplicity[f]/WeylFermionList[[f,3,i]]];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]->ListGauge[[i,3]](ListGauge[[i,3]] - 1)(ListGauge[[i,3]] + 2)/(1/2 ListGauge[[i,3]] (ListGauge[[i,3]] + 1) - 1)];
								];
								(* Anitsymmetric Representation *)
								If[WeylFermionList[[f,3,i]] == 1/2 ListGauge[[i,3]](ListGauge[[i,3]] - 1) + 1,
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 2(ListGauge[[i,3]] + 2) FMultiplicity[f]/WeylFermionList[[f,3,i]]];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]->ListGauge[[i,3]](ListGauge[[i,3]] - 1)(ListGauge[[i,3]] - 2)/(1/2 ListGauge[[i,3]] (ListGauge[[i,3]] - 1) + 1)];
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
					For[s=1, s<=SNumber[], s++,
						(* SU(N) subgroup *)
						If[ListGauge[[i,2]] === SU,
							If[RealScalarList[[s,3,i]] === 1,
								subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 0];
								Continue[];,
								(* Fundamental Representation *)
								If[RealScalarList[[s,3,i]] == ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/2 (Sqr[RealScalarList[[s,3,i]]]-1)/RealScalarList[[s,3,i]]];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/2 SMultiplicity[s]/RealScalarList[[s,3,i]]];
								];
								(* Adjoint Representation *)
								If[RealScalarList[[s,3,i]] == Sqr[ListGauge[[i,3]]] - 1,
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> SMultiplicity[s]/RealScalarList[[s,3,i]] ListGauge[[i,3]]];
								];
								(* Symmetric Representation *)
								If[RealScalarList[[s,3,i]] == 1/2 ListGauge[[i,3]] (ListGauge[[i,3]] + 1),
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> (ListGauge[[i,3]] + 2)(ListGauge[[i,3]] - 1)/ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> SMultiplicity[s]/RealScalarList[[s,3,i]] (1/2 ListGauge[[i,3]] + 1)];
								];
								(* Antisymmetric Representation *)
								If[RealScalarList[[s,3,i]] == 1/2 ListGauge[[i,3]] (ListGauge[[i,3]] - 1),
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
								If[RealScalarList[[s,3,i]] == ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> (ListGauge[[i,3]] - 1)];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 2 SMultiplicity[s]/RealScalarList[[s,3,i]]];
								];
								(* Adjoint Representation *)
								If[RealScalarList[[s,3,i]] == 1/2 ListGauge[[i,3]](ListGauge[[i,3]] - 1),
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> (2 ListGauge[[i,3]] - 4)];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> (2 ListGauge[[i,3]] - 4) SMultiplicity[s]/RealScalarList[[s,3,i]]];
								];
								(* Symmetric Representation *)
								If[RealScalarList[[s,3,i]] == 1/2 ListGauge[[i,3]](ListGauge[[i,3]] + 1) - 1,
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 2(ListGauge[[i,3]] + 2) SMultiplicity[s]/RealScalarList[[s,3,i]]];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]->ListGauge[[i,3]](ListGauge[[i,3]] - 1)(ListGauge[[i,3]] + 2)/(1/2 ListGauge[[i,3]] (ListGauge[[i,3]] + 1) - 1)];
								];
								(* Anitsymmetric Representation *)
								If[RealScalarList[[s,3,i]] == 1/2 ListGauge[[i,3]](ListGauge[[i,3]] - 1) + 1,
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 2(ListGauge[[i,3]] + 2) SMultiplicity[s]/RealScalarList[[s,3,i]]];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]->ListGauge[[i,3]](ListGauge[[i,3]] - 1)(ListGauge[[i,3]] - 2)/(1/2 ListGauge[[i,3]] (ListGauge[[i,3]] - 1) + 1)];
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
				(* Gauge-Yukawa Invariants *)
				If[WeylFermionList != {} && ListYukawa != {} && RealScalarList != {},
					(*subInvariants = Append[subInvariants, Y4[F, ListGauge[[i,1]]]-> (1/d[ListGauge[[i,1]]] Sum[ (YukawaTrace[C2[F, i], Yuk[ss], adj[Yuk[ss]], Join[{KroneckerDelta[#3, #5] KroneckerDelta[#4, #6] &}, Table[KroneckerDelta[#2, #3]&, {ii, NumberOfSubgroups}]]]) , {ss, 1, SNumber[]}])//.{tr[a___, C2[b___], c___]:>(C2[b] tr[a,c]), tr[adj[a_],b_]:>tr[b,adj[a]], tr[adj[a_],b_,adj[c_],d_]:>tr[b,adj[c],d,adj[a]], C2[A___][i1_, i2_]:>C2[A] KroneckerDelta[i1,i2]}];*)
					subInvariants = Append[subInvariants, Y4[F, ListGauge[[i,1]]]-> (1/d[ListGauge[[i,1]]])Sum[
						Sum@@Join[
							{
								SolveTrace3Fast[C2[F,i], Yuk[sIdx[0]], adj[Yuk[sIdx[0]]], Prepend[
									Function[{x}, {1,sIdx[2+x],sIdx[2+x]}]/@Range[NumberOfSubgroups],
									{1,1,sIdx[1],sIdx[2],sIdx[1],sIdx[2]}
								]],
								{sIdx[1], 1, RealScalarList[[sIdx[0],2,1]]},
								{sIdx[2], 1, RealScalarList[[sIdx[0],2,2]]}
							},
							Function[{x}, {sIdx[2+x],1,SMultiplicity[sIdx[0],x]}]/@Range[NumberOfSubgroups]
						],
						{sIdx[0], 1, SNumber[]}
					]//.{tr[a___, C2[b___], c___]:>(C2[b] tr[a,c]), tr[adj[a_],b_]:>tr[b,adj[a]], tr[adj[a_],b_,adj[c_],d_]:>tr[b,adj[c],d,adj[a]], C2[A___][i1_, i2_]:>C2[A] KroneckerDelta[i1,i2]}],
					subInvariants = Append[subInvariants, Y4[F, ListGauge[[i,1]]]->0];
				];
			];
		];
		
		(* Kronecker delta for arbitray list of arguments*)
		TensorDelta[{},{}] := 1;
		TensorDelta[a_List, b_List] := KroneckerDelta[a[[1]], b[[1]]] TensorDelta[Delete[a,1], Delete[b,1]];
		(* Delta symbol for complex scalars corresponding to real/imaginary parts *)
		ComplexDelta[a_, b_] := If[(MatchQ[a, Im[_]] || MatchQ[a, Re[_]]) && (MatchQ[b, Im[_]] || MatchQ[b, Re[_]]) && (a[[1]] === b[[1]]), 1, 0 ];
		
		(* Matrix multiplication and traces for Yukawas *)
		subProd := {
			prod[a___, b_ + c_, d___]:>(prod[a, b, d] + prod[a, c, d]),
			prod[][i1_,i2_]:>KroneckerDelta[i1,i2],
			prod[]:>1,
			prod[a_][i1_,i2_]:>a[i1,i2], 
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
			prod[adj[a___,b___]]:>prod[adj[b],adj[a]],
			tr[adj[a___,b___]]:>tr[adj[b],adj[a]],
			adj[n_ a_]:> (Conjugate[n] adj[a]) /; NumberQ[n],
			prod[a___, tr[b___], c___]:>(tr[b] prod[a,c]),
			tr[a___ prod[b___]]:>(a tr[b]),
			adj[a_][i1_, i2_]:>adj[a[i2, i1]],
			adj[adj[a_]]:>a,
			adj[a_+ b_] :> (adj[a] + adj[b]),
			adj[0]->0
		};
		
		(* replaces Yukawas and other Invariants in Fermion traces and products *)
		subYuk := {
			Yuk[a_][i1_, i2_]:>
				Block[
					{posY, posYadj},
					posY = {};
					posYadj = {};
					If[ListYukawa != {},
						For[yuk = 1, yuk <= Dimensions[ListYukawa][[1]], yuk++,
							If[
								ListYukawa[[yuk,2]] == a && ListYukawa[[yuk,3]] == i1 && ListYukawa[[yuk,4]] == i2, 
								posY = Append[posY, yuk];
							];
						];
					];
					If[ListYukawa != {},
						For[yuk = 1, yuk <= Dimensions[ListYukawa][[1]], yuk++,
							If[
								ListYukawa[[yuk,2]] == a && ListYukawa[[yuk,3]] == i2 && ListYukawa[[yuk,4]] == i1, 
								posYadj = Append[posYadj, yuk];
							];
						];
					];
					If[posY != {}, Plus@@(Function[{x}, Hold[Yukawa[x]]]/@posY), 0] +  If[posYadj != {}, Plus@@(Function[{x}, adj[Hold[Yukawa[x]]]]/@posYadj), 0]
				],
				
			adj[Yukawa[pos_]]:>Join[
				{{adj[ListYukawa[[pos,1]]]//.subProd, Evaluate[Refine[Conjugate[ListYukawa[[pos,6]][#2,#1,#4,#3]]]]&, RealScalarList[[ListYukawa[[pos, 2]], 2, 2]], RealScalarList[[ListYukawa[[pos, 2]], 2, 1]], WeylFermionList[[ListYukawa[[pos, 4]], 2]], WeylFermionList[[ListYukawa[[pos, 3]], 2]]}},
				Function[
					{x},
					Join[
						{Evaluate[Refine[Conjugate[ListYukawa[[pos, 5, x]][#1,#3,#2]]]]&}, 
						If[
							ListGauge[[x, 3]] === 1, 
							{1, 1, 1}, 
							{RealScalarList[[ListYukawa[[pos, 2]], 3, x]], WeylFermionList[[ListYukawa[[pos, 4]], 3, x]], WeylFermionList[[ListYukawa[[pos, 3]], 3, x]]}
						]
					]
				]/@Range[NumberOfSubgroups]
			],
			
			Yukawa[pos_]:>Join[
				{{ListYukawa[[pos,1]]//.subProd, ListYukawa[[pos,6]], RealScalarList[[ListYukawa[[pos, 2]], 2, 1]], RealScalarList[[ListYukawa[[pos, 2]], 2, 2]], WeylFermionList[[ListYukawa[[pos, 3]], 2]], WeylFermionList[[ListYukawa[[pos, 4]], 2]]}},
				Function[
					{x},
					Join[
						{ListYukawa[[pos, 5, x]]}, 
						If[
							ListGauge[[x, 3]] === 1, 
							{1, 1, 1}, 
							{RealScalarList[[ListYukawa[[pos, 2]], 3, x]], WeylFermionList[[ListYukawa[[pos, 3]], 3, x]], WeylFermionList[[ListYukawa[[pos, 4]], 3, x]]}
						]
					]
				]/@Range[NumberOfSubgroups]
			],
			
			C2[F, igauge_][i1_, i2_] :> If[i1 == i2, C2F[i1, igauge], 0],
			C2F[ferm_, igauge_] :> Join[
				{{C2[WeylFermionList[[ferm, 1]], ListGauge[[igauge, 1]]], Mat[1]&, 1, 1, WeylFermionList[[ferm,2]], WeylFermionList[[ferm,2]]}},
				Function[{x}, If[ListGauge[[x, 3]] === 1, {1&, 1, 1, 1}, {KroneckerDelta[#2, #3]&, 1, WeylFermionList[[ferm, 3, x]], WeylFermionList[[ferm, 3, x]]}]]/@Range[NumberOfSubgroups]
			]
		};
		
		(* substitution rule for scalar sector *)
		subQuart := {
			Quartic[a_, b_, c_, d_] :> Block[
				{pos, qq},
				pos = {};
				If[ListQuartic != {},
					For[qq=1, qq<=Dimensions[ListQuarticSym][[1]], qq++,
						If[ListQuarticSym[[qq,2]] == a && ListQuarticSym[[qq,3]] == b && ListQuarticSym[[qq, 4]] == c && ListQuarticSym[[qq,5]] == d,
							pos = Append[pos, qq];
						];
					];
				];
				If[pos == {}, 
					0,
					Plus@@(Hold/@(Quart/@pos))
				]
			],
			Quart[q_] :> Join[
				{{ListQuarticSym[[q,1]], ListQuarticSym[[q,7]], RealScalarList[[ListQuarticSym[[q,2]], 2, 1]], RealScalarList[[ListQuarticSym[[q,2]], 2, 2]], RealScalarList[[ListQuarticSym[[q,3]], 2, 1]], RealScalarList[[ListQuarticSym[[q,3]], 2, 2]], RealScalarList[[ListQuarticSym[[q,4]], 2, 1]], RealScalarList[[ListQuarticSym[[q,4]], 2, 2]], RealScalarList[[ListQuarticSym[[q,5]], 2, 1]], RealScalarList[[ListQuarticSym[[q,5]], 2, 2]]}}, 
				Function[{x}, If[ListGauge[[x,3]] === 1, {ListQuarticSym[[q,6,x]], 1, 1, 1, 1}, {ListQuarticSym[[q,6,x]], RealScalarList[[ListQuarticSym[[q,2]], 3, x]], RealScalarList[[ListQuarticSym[[q,3]], 3, x]], RealScalarList[[ListQuarticSym[[q,4]], 3, x]], RealScalarList[[ListQuarticSym[[q,5]], 3, x]]}]]/@Range[NumberOfSubgroups]
			]
		};
		
		subScalarInvariants := {
			\[CapitalLambda]2[pa_, pb_, pc_, pd_] :> Block[
				{s1, s2},
				sum=0;
				For[s1=1, s1<=SNumber[], s1++,
					For[s2=1, s2<=SNumber[], s2++,
						sum += (ReleaseHold[
								prod[
									Quartic[pa[[1]], pb[[1]], s1, s2], 
									Quartic[s1, s2, pc[[1]], pd[[1]]]
								]/.subQuart//.subProd
							]//.subQuart/.{prod[A_List, B_List]:>(SolveSProd2[A, B, Join[{KroneckerDelta[#1, pa[[2]]] KroneckerDelta[#2, pa[[3]]] KroneckerDelta[#3, pb[[2]]] KroneckerDelta[#4, pb[[3]]] KroneckerDelta[#5, #9] KroneckerDelta[#6, #10] KroneckerDelta[#7, #11] KroneckerDelta[#8, #12] &}, Function[{x}, (KroneckerDelta[pa[[x+3]], #1] KroneckerDelta[pb[[x+3]], #2] KroneckerDelta[#3, #5] KroneckerDelta[#4, #6] KroneckerDelta[pc[[x+3]], #7] KroneckerDelta[pd[[x+3]], #8])&]/@Range[NumberOfSubgroups]]])}
						);
					];
				];
				sum
			],
			H[pa_, pb_, pc_, pd_] :> YukawaTrace[Yuk[pa[[1]]], adj[Yuk[pb[[1]]]], Yuk[pc[[1]]], adj[Yuk[pd[[1]]]], Join[{KroneckerDelta[#1, pa[[2]]] KroneckerDelta[#2, pa[[3]]] KroneckerDelta[#3, pb[[2]]] KroneckerDelta[#4, pb[[3]]] KroneckerDelta[#5, pc[[2]]] KroneckerDelta[#6, pc[[3]]] KroneckerDelta[#7, pd[[2]]] KroneckerDelta[#8, pd[[3]]] &}, Function[
				{x},
				(KroneckerDelta[#1,pa[[3+x]]] KroneckerDelta[#2,pb[[3+x]]] KroneckerDelta[#3,pc[[3+x]]] KroneckerDelta[#4,pd[[3+x]]])&
			]/@Range[NumberOfSubgroups]]],
			\[CapitalLambda]Y[pa_, pb_, pc_, pd_] :> ReleaseHold[
				BetaQuartic[pa[[1]], pb[[1]], pc[[1]], pd[[1]], pa[[2;;]], pb[[2;;]], pc[[2;;]], pd[[2;;]], 0] Hold[
					YukawaTrace[Yuk[pa[[1]]], adj[Yuk[pa[[1]]]], Join[{KroneckerDelta[#1, pa[[2]]] KroneckerDelta[#2, pa[[3]]] KroneckerDelta[#3, #1] KroneckerDelta[#4, #2] &}, Function[{x}, KroneckerDelta[#1,#2] KroneckerDelta[#1, pa[[x+3]]] &]/@Range[NumberOfSubgroups]]] + 
					YukawaTrace[Yuk[pb[[1]]], adj[Yuk[pb[[1]]]], Join[{KroneckerDelta[#1, pb[[2]]] KroneckerDelta[#2, pb[[3]]] KroneckerDelta[#3, #1] KroneckerDelta[#4, #2] &}, Function[{x}, KroneckerDelta[#1,#2] KroneckerDelta[#1, pb[[x+3]]] &]/@Range[NumberOfSubgroups]]] +
					YukawaTrace[Yuk[pc[[1]]], adj[Yuk[pc[[1]]]], Join[{KroneckerDelta[#1, pc[[2]]] KroneckerDelta[#2, pc[[3]]] KroneckerDelta[#3, #1] KroneckerDelta[#4, #2] &}, Function[{x}, KroneckerDelta[#1,#2] KroneckerDelta[#1, pc[[x+3]]] &]/@Range[NumberOfSubgroups]]] + 
					YukawaTrace[Yuk[pd[[1]]], adj[Yuk[pd[[1]]]], Join[{KroneckerDelta[#1, pd[[2]]] KroneckerDelta[#2, pd[[3]]] KroneckerDelta[#3, #1] KroneckerDelta[#4, #2] &}, Function[{x}, KroneckerDelta[#1,#2] KroneckerDelta[#1, pd[[x+3]]] &]/@Range[NumberOfSubgroups]]]
				]
			],
			\[CapitalLambda]S[gaug_][pa_, pb_, pc_, pd_] :> ReleaseHold[
				BetaQuartic[pa[[1]], pb[[1]], pc[[1]], pd[[1]], pa[[2;;]], pb[[2;;]], pc[[2;;]], pd[[2;;]], 0] Hold[
					C2[RealScalarList[[pa[[1]],1]], ListGauge[[gaug,1]]] +
					C2[RealScalarList[[pb[[1]],1]], ListGauge[[gaug,1]]] +
					C2[RealScalarList[[pc[[1]],1]], ListGauge[[gaug,1]]] +
					C2[RealScalarList[[pd[[1]],1]], ListGauge[[gaug,1]]]
				]
			],
			As[gaug1_, gaug2_][a_, b_, c_, d_] :> Block[
				{ind1, ind2, ind1L, ind2L, sum, x},
				sum = 0;
				ind1L = ind1/@Range[0,NumberOfSubgroups+2];
				ind2L = ind2/@Range[0,NumberOfSubgroups+2];
				For[ind1[0]=1, ind1[0]<=SNumber[], ind1[0]++,
					For[ind2[0]=1, ind2[0]<=SNumber[], ind2[0]++,
						sum += Sum@@Join[
							{\[CapitalLambda][gaug1][a, c, ind1L, ind2L] \[CapitalLambda][gaug2][ind1L, ind2L, b, d] + \[CapitalLambda][gaug1][a, ind1L, ind2L, d] \[CapitalLambda][gaug2][ind1L, b, c, ind2L],
							{ind1[1], 1, RealScalarList[[ind1[0], 2,1]]},
							{ind2[1], 1, RealScalarList[[ind1[0], 2,1]]},
							{ind1[2], 1, RealScalarList[[ind1[0], 2,2]]},
							{ind2[2], 1, RealScalarList[[ind1[0], 2,2]]}},
							Function[{x}, {ind1[x+2], 1, SMultiplicity[ind1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ind2[x+2], 1, SMultiplicity[ind2[0], x]}]/@Range[NumberOfSubgroups]
						]//.sub\[CapitalLambda]S;
					];
				];
				sum
			],
			Y2S[pa_, pb_] :> 1/2 (YukawaTrace[adj[Yuk[pa[[1]]]], Yuk[pb[[1]]], Join[{KroneckerDelta[#1, pa[[2]]] KroneckerDelta[#2, pa[[3]]] KroneckerDelta[#3, pb[[2]]] KroneckerDelta[#4, pb[[3]]] &}, Function[{x}, KroneckerDelta[#1, pa[[x+3]]] KroneckerDelta[#2, pb[[x+3]]] &]/@Range[NumberOfSubgroups]]] + YukawaTrace[adj[Yuk[pb[[1]]]], Yuk[pa[[1]]], Join[{KroneckerDelta[#1, pb[[2]]] KroneckerDelta[#2, pb[[3]]] KroneckerDelta[#3, pa[[2]]] KroneckerDelta[#4, pa[[3]]] &}, Function[{x}, KroneckerDelta[#1, pb[[x+3]]] KroneckerDelta[#2, pa[[x+3]]] &]/@Range[NumberOfSubgroups]]]),
			\[CapitalLambda]2S[pa_, pb_] :> Block[
				{s1, s2, s3, sum},
				sum=0;
				For[s1=1, s1<=SNumber[], s1++,
					For[s2=1, s2<=SNumber[], s2++,
						For[s3=1, s3<=SNumber[], s3++,
							sum += (ReleaseHold[
									prod[
										Quartic[pa[[1]], s1, s2, s3], 
										Quartic[pb[[1]], s1, s2, s3]
									]/.subQuart//.subProd
								]//.subQuart/.{prod[A_List, B_List]:>(SolveSProd2[A, B, Join[{KroneckerDelta[#1, pa[[2]]] KroneckerDelta[#2, pa[[3]]] KroneckerDelta[#3, #11] KroneckerDelta[#4, #12] KroneckerDelta[#5, #13] KroneckerDelta[#6, #14] KroneckerDelta[#7, #15] KroneckerDelta[#8, #16] KroneckerDelta[#9, pb[[2]]] KroneckerDelta[#10, pb[[3]]] &}, Function[{x}, (KroneckerDelta[pa[[x+3]], #1] KroneckerDelta[pb[[x+3]], #5] KroneckerDelta[#2, #6] KroneckerDelta[#3, #7] KroneckerDelta[#4, #8])&]/@Range[NumberOfSubgroups]]])}
							);
						];
					];
				];
				Sqr[24]/6 sum
			],
			H2S[pa_, pb_] :> Block[
				{ss,x},
				1/2 Sum[YukawaTrace[Yuk[pa[[1]]], adj[Yuk[pb[[1]]]], Yuk[ss], adj[Yuk[ss]], Join[{KroneckerDelta[#1, pa[[2]]] KroneckerDelta[#2, pa[[3]]] KroneckerDelta[#3, pb[[2]]] KroneckerDelta[#4, pb[[3]]] KroneckerDelta[#5, #7] KroneckerDelta[#6,#8] &}, Function[{x}, KroneckerDelta[#1, pa[[x+3]]] KroneckerDelta[#2, pb[[x+3]]] KroneckerDelta[#3,#4] &]/@Range[NumberOfSubgroups]]] + YukawaTrace[Yuk[pb[[1]]], adj[Yuk[pa[[1]]]], Yuk[ss], adj[Yuk[ss]], Join[{KroneckerDelta[#1, pb[[2]]] KroneckerDelta[#2, pb[[3]]] KroneckerDelta[#3, pa[[2]]] KroneckerDelta[#4, pa[[3]]] KroneckerDelta[#5, #7] KroneckerDelta[#6,#8] &}, Function[{x}, KroneckerDelta[#1, pb[[x+3]]] KroneckerDelta[#2, pa[[x+3]]] KroneckerDelta[#3,#4] &]/@Range[NumberOfSubgroups]]], {ss, 1, SNumber[]}]	
			],
			Hbar2S[pa_, pb_] :> Block[
				{ss,x},
				1/2 Sum[YukawaTrace[Yuk[pa[[1]]], adj[Yuk[ss]], Yuk[pb[[1]]], adj[Yuk[ss]], Join[{KroneckerDelta[#1, pa[[2]]] KroneckerDelta[#2, pa[[3]]] KroneckerDelta[#3,#7] KroneckerDelta[#4,#8] KroneckerDelta[#5, pb[[2]]] KroneckerDelta[#6, pb[[3]]] &}, Function[{x}, KroneckerDelta[#1, pa[[x+3]]] KroneckerDelta[#3, pb[[x+3]]] KroneckerDelta[#2,#4] &]/@Range[NumberOfSubgroups]]] + YukawaTrace[adj[Yuk[pa[[1]]]], Yuk[ss], adj[Yuk[pb[[1]]]], Yuk[ss], Join[{KroneckerDelta[#1, pa[[2]]] KroneckerDelta[#2, pa[[3]]] KroneckerDelta[#3,#7] KroneckerDelta[#4,#8] KroneckerDelta[#5, pb[[2]]] KroneckerDelta[#6, pb[[3]]] &}, Function[{x}, KroneckerDelta[#1, pa[[x+3]]] KroneckerDelta[#3, pb[[x+3]]] KroneckerDelta[#2,#4] &]/@Range[NumberOfSubgroups]]], {ss, 1, SNumber[]}]	
			],
			Y2FS[gauge_, pa_, pb_] :> 1/2(YukawaTrace[C2[F, gauge], Yuk[pa[[1]]], adj[Yuk[pb[[1]]]], Join[{KroneckerDelta[#3, pa[[2]]] KroneckerDelta[#4, pa[[3]]] KroneckerDelta[#5, pb[[2]]] KroneckerDelta[#6, pb[[3]]] &}, Function[{x}, KroneckerDelta[#1,1] KroneckerDelta[#2, pa[[3+x]]] KroneckerDelta[#3, pb[[3+x]]] &]/@Range[NumberOfSubgroups]]] + YukawaTrace[C2[F, gauge], Yuk[pb[[1]]], adj[Yuk[pa[[1]]]], Join[{KroneckerDelta[#3, pb[[2]]] KroneckerDelta[#4, pb[[3]]] KroneckerDelta[#5, pa[[2]]] KroneckerDelta[#6, pa[[3]]] &}, Function[{x}, KroneckerDelta[#1,1] KroneckerDelta[#2, pb[[3+x]]] KroneckerDelta[#3, pa[[3+x]]] &]/@Range[NumberOfSubgroups]]]),
			H2t[gauge_, pa_, pi_, pj_] :> Module[
				{ss, ff1, ff2, ff3, ff4, scGenIdx, scGenIdx2, scGaugeIdx, a, A, B, C},
				Sum[
					ReleaseHold[(ReleaseHold[SolveProd[Yuk[pa[[1]]], adj[Yuk[ss]], Yuk[ss], pi[[1]], pj[[1]]] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]/.{prod[A___, adj[Yukawa[a_]]]:>prod[A, adj[Yukawa[a]]][ListYukawa[[a,4]]], prod[A___, Yukawa[a_]]:>prod[A, Yukawa[a]][ListYukawa[[a,3]]]}//.subYuk //.{
						prod[A_, B_, C_][a_] :> Sum@@Join[
							{
								Refine[Sum[GetGenProd[{A,B,C}, {pa[[2]], scGenIdx, scGenIdx2, scGenIdx, scGenIdx2}, pi[[2]], pj[[2]]] //.subProd, {scGenIdx, 1, C[[1,3]]}, {scGenIdx2, 1, C[[1,4]]}]] Refine[Conjugate[\[CapitalLambda][gauge][pi, Join[{a,1},ff3/@Range[NumberOfSubgroups]], Join[pi[[1;;2]], ff1/@Range[NumberOfSubgroups]], Join[{a,1},ff4/@Range[NumberOfSubgroups]]] //.sub\[CapitalLambda]F]] Times@@Function[{x}, A[[x+1, 1]][pa[[x+2]], ff1[x], ff2[x]] B[[x+1,1]][scGaugeIdx[x], ff2[x], ff3[x]] C[[x+1,1]][scGaugeIdx[x], ff4[x], pj[[x+2]]]]/@Range[NumberOfSubgroups]
							},
							Function[{x},{scGaugeIdx[x], 1, C[[x+1, 2]]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff1[x], 1, A[[x+1,3]]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff2[x], 1, A[[x+1,4]]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff3[x], 1, B[[x+1,4]]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff4[x], 1, C[[x+1,3]]}]/@Range[NumberOfSubgroups]
						]
					})] + 
					ReleaseHold[(ReleaseHold[SolveProd[Yuk[ss], adj[Yuk[ss]], Yuk[pa[[1]]], pi[[1]], pj[[1]]] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]/.{prod[adj[Yukawa[a_]], A___]:>prod[adj[Yukawa[a]], A][ListYukawa[[a,3]]], prod[Yukawa[a_], A___]:>prod[Yukawa[a], A][ListYukawa[[a,4]]]}//.subYuk //.{
						prod[A_, B_, C_][a_] :> Sum@@Join[
							{
								Refine[Sum[GetGenProd[{A,B,C}, {scGenIdx, scGenIdx2, scGenIdx, scGenIdx2, pa[[2]], pa[[3]]}, pi[[2]], pj[[2]]] //.subProd, {scGenIdx, 1, A[[1,3]]}, {scGenIdx2, 1, A[[1,4]]}]] (\[CapitalLambda][gauge][Join[{a,1},ff1/@Range[NumberOfSubgroups]], Join[pj[[1;;2]], ff4/@Range[NumberOfSubgroups]], Join[{a,1},ff2/@Range[NumberOfSubgroups]], pj] //.sub\[CapitalLambda]F) Times@@Function[{x}, A[[x+1, 1]][scGaugeIdx[x], pi[[x+2]], ff1[x]] B[[x+1,1]][scGaugeIdx[x], ff2[x], ff3[x]] C[[x+1,1]][pa[[x+3]], ff3[x], ff4[x]]]/@Range[NumberOfSubgroups]
							},
							Function[{x},{scGaugeIdx[x], 1, A[[x+1, 2]]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff1[x], 1, A[[x+1,4]]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff2[x], 1, B[[x+1,3]]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff3[x], 1, B[[x+1,4]]}]/@Range[NumberOfSubgroups],
							Function[{x},{ff4[x], 1, C[[x+1,4]]}]/@Range[NumberOfSubgroups]
						]
					})],
					{ss, 1, SNumber[]}
				]
			],
			\[CapitalLambda]bar3[pa_, pb_, pc_, pd_] :> Block[
				{s1, s2, s3, s4, sum},
				sum=0;
				For[s1=1, s1<=SNumber[], s1++,
					For[s2=1, s2<=SNumber[], s2++,
						For[s3=1, s3<=SNumber[], s3++,
							For[s4=1, s4<=SNumber[], s4++,
								sum += (ReleaseHold[
										prod[
											Quartic[pa[[1]], pb[[1]], s1, s2], 
											Quartic[pc[[1]], s1, s3, s4], 
											Quartic[pd[[1]], s2, s3, s4]
										]/.subQuart//.subProd
									]//.subQuart/.{prod[A_List, B_List, C_List]:>(SolveSProd3[A, B, C, Join[{KroneckerDelta[#1, pa[[2]]] KroneckerDelta[#2, pa[[3]]] KroneckerDelta[#3, pb[[2]]] KroneckerDelta[#4, pb[[3]]] KroneckerDelta[#5, #11] KroneckerDelta[#6, #12] KroneckerDelta[#7, #19] KroneckerDelta[#8, #20] KroneckerDelta[#9, pc[[2]]] KroneckerDelta[#10, pc[[3]]] KroneckerDelta[#13, #21] KroneckerDelta[#14, #22] KroneckerDelta[#15, #23] KroneckerDelta[#16, #24] &}, Function[{x}, (KroneckerDelta[pa[[x+3]], #1] KroneckerDelta[pb[[x+3]], #2] KroneckerDelta[#3, #6] KroneckerDelta[#4, #10] KroneckerDelta[pc[[x+3]], #5] KroneckerDelta[pd[[x+3]], #9] KroneckerDelta[#7, #11] KroneckerDelta[#8,#12])&]/@Range[NumberOfSubgroups]]])}
								);
							];
						];
					];
				];
				sum
			],
			\[CapitalLambda]bar2Y[pa_, pb_, pc_, pd_] :> Block[
				{s1, s2, s3, sum},
				sum=0;
				For[s1[0]=1, s1[0]<=SNumber[], s1[0]++,
					For[s2[0]=1, s2[0]<=SNumber[], s2[0]++,
						For[s3[0]=1, s3[0]<=SNumber[], s3[0]++,
							sum += Sum@@Join[
								{
									(Y2S[s2/@Range[0,NumberOfSubgroups+2], s3/@Range[0,NumberOfSubgroups+2]] /.subScalarInvariants) (
										ReleaseHold[
											prod[
												Quartic[pa[[1]], pb[[1]], s1[0], s2[0]], 
												Quartic[pc[[1]], pd[[1]], s1[0], s3[0]]
											]/.subQuart//.subProd
										]//.subQuart/.{prod[A_List, B_List]:>(SolveSProd2[A, B, Join[{KroneckerDelta[#1, pa[[2]]] KroneckerDelta[#2, pa[[3]]] KroneckerDelta[#3, pb[[2]]] KroneckerDelta[#4, pb[[3]]] KroneckerDelta[#5, #13] KroneckerDelta[#6, #14] KroneckerDelta[#7, s2[1]] KroneckerDelta[#8, s2[2]] KroneckerDelta[#9, pc[[2]]] KroneckerDelta[#10, pc[[3]]] KroneckerDelta[#11, pd[[2]]] KroneckerDelta[#12, pd[[3]]] KroneckerDelta[#15, s3[1]] KroneckerDelta[#16, s3[2]] &}, Function[{x}, (KroneckerDelta[pa[[x+3]], #1] KroneckerDelta[pb[[x+3]], #2] KroneckerDelta[#3, #7] KroneckerDelta[#4, s2[x+2]] KroneckerDelta[pc[[x+3]], #5] KroneckerDelta[pd[[x+3]], #6] KroneckerDelta[#8, s3[x+2]])&]/@Range[NumberOfSubgroups]]])}
									),
									{s2[1], 1, RealScalarList[[s2[0], 2,1]]},
									{s3[1], 1, RealScalarList[[s3[0], 2,1]]},
									{s2[2], 1, RealScalarList[[s2[0], 2,2]]},
									{s3[2], 1, RealScalarList[[s3[0], 2,2]]}
								},
								Function[{x},{s2[x+2], 1, SMultiplicity[s2[0], x]}]/@Range[NumberOfSubgroups],
								Function[{x},{s3[x+2], 1, SMultiplicity[s3[0], x]}]/@Range[NumberOfSubgroups]
							];
						];
					];
				];
				sum
			],
			Hbar\[Lambda][pa_, pb_, pc_, pd_] :> Block[
				{ss1, ss2, sum},
				sum = 0;
				For[ss1[0]=1, ss1[0]<=SNumber[], ss1[0]++,
					For[ss2[0]=1, ss2[0]<=SNumber[], ss2[0]++,
						sum += Sum@@Join[
							{
								BetaQuartic[pa[[1]], pb[[1]], ss1[0], ss2[0], pa[[2;;]], pb[[2;;]], ss1/@Range[NumberOfSubgroups+2], ss2/@Range[NumberOfSubgroups+2], 0] (
									YukawaTrace[Yuk[pc[[1]]], adj[Yuk[ss1[0]]], Yuk[pd[[1]]], adj[Yuk[ss2[0]]], Join[{KroneckerDelta[#1, pc[[2]]] KroneckerDelta[#2, pc[[3]]] KroneckerDelta[#3, ss1[1]] KroneckerDelta[#4, ss1[2]] KroneckerDelta[#5, pd[[2]]] KroneckerDelta[#6, pd[[3]]] KroneckerDelta[#7, ss2[1]] KroneckerDelta[#8, ss2[2]] &}, Function[{x}, KroneckerDelta[#1, pc[[3+x]]] KroneckerDelta[#2,ss1[x+2]] KroneckerDelta[#3, pd[[3+x]]] KroneckerDelta[#4, ss2[2+x]] &]/@Range[NumberOfSubgroups]]] + 
									YukawaTrace[adj[Yuk[pc[[1]]]], Yuk[ss1[0]], adj[Yuk[pd[[1]]]], Yuk[ss2[0]], Join[{KroneckerDelta[#1, pc[[2]]] KroneckerDelta[#2, pc[[3]]] KroneckerDelta[#3, ss1[1]] KroneckerDelta[#4, ss1[2]] KroneckerDelta[#5, pd[[2]]] KroneckerDelta[#6, pd[[3]]] KroneckerDelta[#7, ss2[1]] KroneckerDelta[#8, ss2[2]] &}, Function[{x}, KroneckerDelta[#1, pc[[3+x]]] KroneckerDelta[#2,ss1[2+x]] KroneckerDelta[#3, pd[[3+x]]] KroneckerDelta[#4, ss2[2+x]] &]/@Range[NumberOfSubgroups]]]
								),
								{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
								{ss2[1], 1, RealScalarList[[ss1[0], 2,1]]},
								{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]},
								{ss2[2], 1, RealScalarList[[ss1[0], 2,2]]}
							},
							Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
							Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
						];
					];
				];
				sum
			],
			HY[pa_, pb_, pc_, pd_] :> Block[
				{ss},
				Sum[YukawaTrace[adj[Yuk[ss]], Yuk[ss], adj[Yuk[pa[[1]]]], Yuk[pb[[1]]], adj[Yuk[pc[[1]]]], Yuk[pd[[1]]], Join[{KroneckerDelta[#1,#3] KroneckerDelta[#2,#4] KroneckerDelta[#5, pa[[2]]]  KroneckerDelta[#6, pa[[3]]] KroneckerDelta[#7, pb[[2]]] KroneckerDelta[#8, pb[[3]]] KroneckerDelta[#9, pc[[2]]] KroneckerDelta[#10, pc[[3]]] KroneckerDelta[#11, pd[[2]]] KroneckerDelta[#12, pd[[3]]] &}, Function[{x}, KroneckerDelta[#1,#2] KroneckerDelta[#3, pa[[3+x]]] KroneckerDelta[#4, pb[[x+3]]] KroneckerDelta[#5, pc[[x+3]]] KroneckerDelta[#6, pd[[x+3]]] &]/@Range[NumberOfSubgroups]]],
					{ss, 1, SNumber[]}]
				
			],
			HbarY[pa_, pb_, pc_, pd_] :> Block[
				{ss},
				Sum[(
						YukawaTrace[Yuk[ss], adj[Yuk[pa[[1]]]], Yuk[ss], adj[Yuk[pb[[1]]]], Yuk[pc[[1]]], adj[Yuk[pd[[1]]]], Join[{KroneckerDelta[#1,#5] KroneckerDelta[#2, #6] KroneckerDelta[#3, pa[[2]]] KroneckerDelta[#4, pa[[3]]] KroneckerDelta[#7, pb[[2]]] KroneckerDelta[#8, pb[[3]]] KroneckerDelta[#9, pc[[2]]] KroneckerDelta[#10, pc[[3]]] KroneckerDelta[#11, pd[[2]]] KroneckerDelta[#12, pd[[3]]] &}, Function[{x}, KroneckerDelta[#1, #3] KroneckerDelta[#2, pa[[x+3]]] KroneckerDelta[#4, pb[[x+3]]] KroneckerDelta[#5, pc[[x+3]]] KroneckerDelta[#6, pd[[x+3]]] &]/@Range[NumberOfSubgroups]]] + 
						YukawaTrace[Yuk[pd[[1]]], adj[Yuk[pc[[1]]]], Yuk[pb[[1]]], adj[Yuk[ss]], Yuk[pa[[1]]], adj[Yuk[ss]], Join[{KroneckerDelta[#1, pd[[2]]] KroneckerDelta[#2, pd[[3]]] KroneckerDelta[#3, pc[[2]]] KroneckerDelta[#4, pc[[3]]] KroneckerDelta[#5, pb[[2]]] KroneckerDelta[#6, pb[[3]]] KroneckerDelta[#7,#11] KroneckerDelta[#8, #12] KroneckerDelta[#9, pa[[2]]] KroneckerDelta[#10, pa[[3]]] &} , Function[{x}, KroneckerDelta[#6, #4] KroneckerDelta[#5, pa[[x+3]]] KroneckerDelta[#3, pb[[x+3]]] KroneckerDelta[#2, pc[[x+3]]] KroneckerDelta[#1, pd[[x+3]]] &]/@Range[NumberOfSubgroups]]]
					),
					{ss, 1, SNumber[]}
				]
			],
			H3[pa_, pb_, pc_, pd_] :> Block[
				{ss},
				Sum[
					YukawaTrace[Yuk[pa[[1]]], adj[Yuk[pb[[1]]]], Yuk[ss], adj[Yuk[pc[[1]]]], Yuk[pd[[1]]], adj[Yuk[ss]], Join[{KroneckerDelta[#1, pa[[2]]] KroneckerDelta[#2, pa[[3]]] KroneckerDelta[#3, pb[[2]]] KroneckerDelta[#4, pb[[3]]] KroneckerDelta[#7, pc[[2]]] KroneckerDelta[#8, pc[[3]]] KroneckerDelta[#9, pd[[2]]] KroneckerDelta[#10, pd[[3]]] KroneckerDelta[#5, #11] KroneckerDelta[#6, #12] &}, Function[{x}, KroneckerDelta[#1, pa[[x+3]]] KroneckerDelta[#2, pb[[x+3]]] KroneckerDelta[#3, #6] KroneckerDelta[#4, pc[[x+3]]] KroneckerDelta[#5, pd[[x+3]]] &]/@Range[NumberOfSubgroups]]],
					{ss, 1, SNumber[]}
				]
			],
			\[CapitalLambda]bar2S[gaug_][pa_, pb_, pc_, pd_] :> Block[
				{ss1, ss2},
				Sum[
					Sum@@Join[
						{
							(
								ReleaseHold[
									prod[
										Quartic[pa[[1]], pb[[1]], ss1[0], ss2[0]], 
										Quartic[pc[[1]], pd[[1]], ss1[0], ss2[0]]
									]//.subProd/.subQuart//.subProd
								]//.subQuart/.{prod[A_List, B_List]:>(
									A[[1,1]] B[[1,1]] A[[1,2]][pa[[2]], pa[[3]], pb[[2]], pb[[3]], ss1[1], ss1[2], ss2[1], ss2[2]]  B[[1,2]][pc[[2]], pc[[3]], pd[[2]], pd[[3]], ss1[1], ss1[2], ss2[1], ss2[2]] Times@@(Function[{x}, A[[x+1,1]][pa[[3+x]], pb[[3+x]], ss1[2+x], ss2[2+x]] B[[x+1,1]][pc[[3+x]], pd[[3+x]], ss1[2+x], ss2[2+x]]]/@Range[NumberOfSubgroups])
								)}
							)
							C2[RealScalarList[[ss2[0],1]], ListGauge[[gaug,1]]],
							{ss1[1], 1, RealScalarList[[ss1[0], 2,1]]},
							{ss2[1], 1, RealScalarList[[ss2[0], 2,1]]},
							{ss1[2], 1, RealScalarList[[ss1[0], 2,2]]},
							{ss2[2], 1, RealScalarList[[ss2[0], 2,2]]}
						},
						Function[{x}, {ss1[x+2], 1, SMultiplicity[ss1[0], x]}]/@Range[NumberOfSubgroups],
						Function[{x}, {ss2[x+2], 1, SMultiplicity[ss2[0], x]}]/@Range[NumberOfSubgroups]
					],
					{ss1[0], 1, SNumber[]},
					{ss2[0], 1, SNumber[]}
				]
			],
			\[CapitalLambda]2g[gaug_][pa_, pb_, pc_, pd_] :> Block[
				{ss1, ss2, ss3, ss4},
				Sum[
					Sum@@Join[
						{
							(
								ReleaseHold[
									prod[
										Quartic[pa[[1]], pb[[1]], ss1[0], ss2[0]], 
										Quartic[pc[[1]], pd[[1]], ss3[0], ss4[0]]
									]//.subProd/.subQuart//.subProd
								]//.subQuart/.{prod[A_List, B_List]:>(
									A[[1,1]] B[[1,1]] A[[1,2]][pa[[2]], pa[[3]], pb[[2]], pb[[3]], ss1[1], ss1[2], ss2[1], ss2[2]]  B[[1,2]][pc[[2]], pc[[3]], pd[[2]], pd[[3]], ss3[1], ss3[2], ss4[1], ss4[2]] Times@@(Function[{x}, A[[x+1,1]][pa[[3+x]], pb[[3+x]], ss1[2+x], ss2[2+x]] B[[x+1,1]][pc[[3+x]], pd[[3+x]], ss3[2+x], ss4[2+x]]]/@Range[NumberOfSubgroups])
								)}
							)
							\[CapitalLambda][gaug][ss1/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]]//.sub\[CapitalLambda]S,
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
					],
					{ss1[0], 1, SNumber[]},
					{ss2[0], 1, SNumber[]},
					{ss3[0], 1, SNumber[]},
					{ss4[0], 1, SNumber[]}
				]
			],
			HF[gaug_][pa_, pb_, pc_, pd_] :>(
				YukawaTrace[C2[F, gaug], Yuk[pa[[1]]], adj[Yuk[pb[[1]]]], Yuk[pc[[1]]], adj[Yuk[pd[[1]]]], Join[{KroneckerDelta[#3, pa[[2]]] KroneckerDelta[#4, pa[[3]]] KroneckerDelta[#5, pb[[2]]] KroneckerDelta[#6, pb[[3]]] KroneckerDelta[#7, pc[[2]]] KroneckerDelta[#8, pc[[3]]] KroneckerDelta[#9, pd[[2]]] KroneckerDelta[#10, pd[[3]]] &}, Function[{x}, KroneckerDelta[#1,1] KroneckerDelta[#2, pa[[x+3]]] KroneckerDelta[#3, pb[[x+3]]] KroneckerDelta[#4, pc[[x+3]]] KroneckerDelta[#5, pd[[x+3]]] &]/@Range[NumberOfSubgroups]]] + 
				YukawaTrace[ C2[F,gaug], adj[Yuk[pb[[1]]]], Yuk[pc[[1]]], adj[Yuk[pd[[1]]]], Yuk[pa[[1]]], Join[{KroneckerDelta[#3, pb[[2]]] KroneckerDelta[#4, pb[[3]]] KroneckerDelta[#5, pc[[2]]] KroneckerDelta[#6, pc[[3]]] KroneckerDelta[#7, pd[[2]]] KroneckerDelta[#8, pd[[3]]] KroneckerDelta[#9, pa[[2]]] KroneckerDelta[#10, pa[[3]]] &}, Function[{x}, KroneckerDelta[#1,1] KroneckerDelta[#5, pa[[x+3]]] KroneckerDelta[#2, pb[[x+3]]] KroneckerDelta[#3, pc[[x+3]]] KroneckerDelta[#4, pd[[x+3]]] &]/@Range[NumberOfSubgroups]]]
			)/.{tr[A___,C2[B___], C___]:>C2[B] tr[A,C]},
			A\[Lambda][gauge_, gauge2_][a_, b_, c_, d_] :> Block[
				{ss1, ss2, ss3, ss4},
				Sum[
					Sum@@Join[
						{
							BetaQuartic[a[[1]], b[[1]], ss1[0], ss2[0], a[[2;;]], b[[2;;]], ss1/@Range[NumberOfSubgroups+2], ss2/@Range[NumberOfSubgroups+2], 0](
								\[CapitalLambda][gauge, gauge2][ss1/@Range[0,NumberOfSubgroups+2], c, ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge2, gauge][ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2], d] +
								\[CapitalLambda][gauge, gauge2][ss1/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], d] \[CapitalLambda][gauge2, gauge][ss3/@Range[0,NumberOfSubgroups+2], c, ss2/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] +
								\[CapitalLambda][gauge,gauge2][ss3/@Range[0,NumberOfSubgroups+2], c, ss2/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge2, gauge][ss1/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], d] +
								\[CapitalLambda][gauge, gauge2][ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2], d] \[CapitalLambda][gauge2, gauge][ss1/@Range[0,NumberOfSubgroups+2], c, ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]]
							)//.sub\[CapitalLambda]S,
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
					],
					{ss1[0], 1, SNumber[]},
					{ss2[0], 1, SNumber[]},
					{ss3[0], 1, SNumber[]},
					{ss4[0], 1, SNumber[]}
				]
			],
			Abar\[Lambda][gauge_, gauge2_][a_, b_, c_, d_] :> Block[
				{ss1, ss2, ss3, ss4},
				Sum[
					Sum@@Join[
						{
							BetaQuartic[a[[1]], b[[1]], ss1[0], ss2[0], a[[2;;]], b[[2;;]], ss1/@Range[NumberOfSubgroups+2], ss2/@Range[NumberOfSubgroups+2], 0](
								\[CapitalLambda][gauge, gauge2][c, d, ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge2, gauge][ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss1/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2]] +
								\[CapitalLambda][gauge, gauge2][c, ss4/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge2, gauge][ss3/@Range[0,NumberOfSubgroups+2], d, ss1/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] +
								\[CapitalLambda][gauge, gauge2][ss3/@Range[0,NumberOfSubgroups+2], d, ss1/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge2, gauge][c, ss4/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2]] +
								\[CapitalLambda][gauge, gauge2][ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss1/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge2, gauge][c, d, ss3/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]]
							)//.sub\[CapitalLambda]S,
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
					],
					{ss1[0], 1, SNumber[]},
					{ss2[0], 1, SNumber[]},
					{ss3[0], 1, SNumber[]},
					{ss4[0], 1, SNumber[]}
				]
			],
			BY[gauge_, gauge2_][a_, b_, c_, d_] :> Block[
				{ff, gg, ff1, ff2, ff3, ff4},
				(
					ReleaseHold[(ReleaseHold[SolveTrace[Yuk[c[[1]]], adj[Yuk[d[[1]]]]]//. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]/.{tr[adj[Yukawa[aa_]], A___]:>tr[adj[Yukawa[aa]], A][ListYukawa[[aa,4]]], tr[Yukawa[aa_], A___]:>tr[Yukawa[aa], A][ListYukawa[[aa,3]]]}//.subYuk //.{tr[A_, B_][ff_]:> Sum[Sum[Sum@@Join[
						{
							GetGenTrace[{A,B}, {{c[[2]], c[[3]]}, {d[[2]], d[[3]]}}] ((
								\[CapitalLambda][gauge, gauge2][gg/@Range[0,NumberOfSubgroups+2], Join[{ff, 1,1}, ff1/@Range[NumberOfSubgroups]], a, Join[{ff, 1,1}, ff2/@Range[NumberOfSubgroups]]] \[CapitalLambda][gauge2, gauge][b, Join[{ff, 1,1}, ff2/@Range[NumberOfSubgroups]], gg/@Range[0,NumberOfSubgroups+2], Join[{ff, 1,1}, ff3/@Range[NumberOfSubgroups]]] + 
								\[CapitalLambda][gauge2, gauge][gg/@Range[0,NumberOfSubgroups+2], Join[{ff, 1,1}, ff2/@Range[NumberOfSubgroups]], a, Join[{ff, 1,1}, ff3/@Range[NumberOfSubgroups]]] \[CapitalLambda][gauge,gauge2][b, Join[{ff, 1,1}, ff1/@Range[NumberOfSubgroups]], gg/@Range[0,NumberOfSubgroups+2], Join[{ff, 1,1}, ff2/@Range[NumberOfSubgroups]]]
							)//.sub\[CapitalLambda]SF) Times@@(Function[{x}, A[[x+1,1]][c[[x+1]], ff3[x], ff4[x]] B[[x+1,1]][d[[x+1]], ff4[x], ff1[x]]]/@Range[NumberOfSubgroups])
						},
						Function[{x}, {ff1[x], 1, A[[x+1,3]]}]/@Range[NumberOfSubgroups],
						Function[{x}, {ff2[x], 1, A[[x+1,3]]}]/@Range[NumberOfSubgroups],
						Function[{x}, {ff3[x], 1, A[[x+1,3]]}]/@Range[NumberOfSubgroups],
						Function[{x}, {ff4[x], 1, A[[x+1,4]]}]/@Range[NumberOfSubgroups],
						Function[{x}, {gg[x+2], 1, SMultiplicity[gg[0], x]}]/@Range[NumberOfSubgroups]
						
					], {gg[1], 1, RealScalarList[[gg[0], 2,1]]}, {gg[2], 1, RealScalarList[[gg[0], 2,2]]}], {gg[0], 1, SNumber[]}]})] + 
					ReleaseHold[(ReleaseHold[SolveTrace[adj[Yuk[d[[1]]]], Yuk[c[[1]]]]//. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]}/.subYuk //.subProd]/.{tr[adj[Yukawa[aa_]], A___]:>tr[adj[Yukawa[aa]], A][ListYukawa[[aa,4]]], tr[Yukawa[aa_], A___]:>tr[Yukawa[aa], A][ListYukawa[[aa,3]]]}//.subYuk //.{tr[A_, B_][ff_]:> Sum[Sum[Sum@@Join[
						{
							GetGenTrace[{A,B}, {{c[[2]], c[[3]]}, {d[[2]], d[[3]]}}] ((
								\[CapitalLambda][gauge,gauge2][a, Join[{ff, 1,1}, ff1/@Range[NumberOfSubgroups]], gg/@Range[0,NumberOfSubgroups+2], Join[{ff, 1,1}, ff2/@Range[NumberOfSubgroups]]] \[CapitalLambda][gauge2,gauge][gg/@Range[0,NumberOfSubgroups+2], Join[{ff, 1,1}, ff2/@Range[NumberOfSubgroups]], b, Join[{ff, 1,1}, ff3/@Range[NumberOfSubgroups]]] + 
								\[CapitalLambda][gauge2,gauge][a, Join[{ff, 1,1}, ff2/@Range[NumberOfSubgroups]], gg/@Range[0,NumberOfSubgroups+2], Join[{ff, 1,1}, ff3/@Range[NumberOfSubgroups]]] \[CapitalLambda][gauge,gauge2][gg/@Range[0,NumberOfSubgroups+2], Join[{ff, 1,1}, ff1/@Range[NumberOfSubgroups]], b, Join[{ff, 1,1}, ff2/@Range[NumberOfSubgroups]]]
							)//.sub\[CapitalLambda]SF) Times@@(Function[{x}, A[[x+1,1]][d[[x+1]], ff3[x], ff4[x]] B[[x+1,1]][c[[x+1]], ff4[x], ff1[x]]]/@Range[NumberOfSubgroups])
						},
						Function[{x}, {ff1[x], 1, A[[x+1,3]]}]/@Range[NumberOfSubgroups],
						Function[{x}, {ff2[x], 1, A[[x+1,3]]}]/@Range[NumberOfSubgroups],
						Function[{x}, {ff3[x], 1, A[[x+1,3]]}]/@Range[NumberOfSubgroups],
						Function[{x}, {ff4[x], 1, A[[x+1,4]]}]/@Range[NumberOfSubgroups],
						Function[{x}, {gg[x+2], 1, SMultiplicity[gg[0], x]}]/@Range[NumberOfSubgroups]
						
					], {gg[1], 1, RealScalarList[[gg[0], 2, 1]]}, {gg[2], 1, RealScalarList[[gg[0], 2, 2]]}], {gg[0], 1, SNumber[]}]})]
				)
			],
			BbarY[gauge_, gauge2_][a_, b_, c_, d_] :> Module[
				{ffA, ffB, gg, ff1, ff2, ff3, ff4},
				(
					ReleaseHold[(ReleaseHold[SolveTrace[Yuk[c[[1]]], adj[Yuk[d[[1]]]]]//.subProd /.subYuk //.subProd]/.{tr[adj[Yukawa[aa_]], A___]:>tr[adj[Yukawa[aa]], A][ListYukawa[[aa,4]], ListYukawa[[aa,3]]], tr[Yukawa[aa_], A___]:>tr[Yukawa[aa], A][ListYukawa[[aa,3]], ListYukawa[[aa,4]]]}//.subYuk //.{tr[A_, B_][ffA_, ffB_]:> Sum[Sum[Sum@@Join[
						{
							GetGenTrace[{A,B}, {{c[[2]], c[[3]]}, {d[[2]], d[[3]]}}] ((
								\[CapitalLambda][gauge,gauge2][gg/@Range[0,NumberOfSubgroups+2], Join[{ffA,1,1}, ff1/@Range[NumberOfSubgroups]], a, Join[{ffA,1,1}, ff2/@Range[NumberOfSubgroups]]] \[CapitalLambda][gauge2, gauge][gg/@Range[0,NumberOfSubgroups+2], Join[{ffB,1,1}, ff3/@Range[NumberOfSubgroups]], b, Join[{ffB,1,1}, ff4/@Range[NumberOfSubgroups]]] +
								\[CapitalLambda][gauge2,gauge][gg/@Range[0,NumberOfSubgroups+2], Join[{ffB,1,1}, ff3/@Range[NumberOfSubgroups]], a, Join[{ffB,1,1}, ff4/@Range[NumberOfSubgroups]]] \[CapitalLambda][gauge, gauge2][gg/@Range[0,NumberOfSubgroups+2], Join[{ffA,1,1}, ff1/@Range[NumberOfSubgroups]], b, Join[{ffA,1,1}, ff2/@Range[NumberOfSubgroups]]]
							)//.sub\[CapitalLambda]SF) Times@@(Function[{x}, A[[x+1,1]][c[[x+1]], ff2[x], ff3[x]] B[[x+1,1]][d[[x+1]], ff4[x], ff1[x]]]/@Range[NumberOfSubgroups])
						},
						Function[{x}, {ff1[x], 1, A[[x+1,3]]}]/@Range[NumberOfSubgroups],
						Function[{x}, {ff2[x], 1, A[[x+1,3]]}]/@Range[NumberOfSubgroups],
						Function[{x}, {ff3[x], 1, A[[x+1,4]]}]/@Range[NumberOfSubgroups],
						Function[{x}, {ff4[x], 1, A[[x+1,4]]}]/@Range[NumberOfSubgroups],
						Function[{x}, {gg[x+2], 1, SMultiplicity[gg[0], x]}]/@Range[NumberOfSubgroups]
					],{gg[1], 1, RealScalarList[[gg[0], 2,1]]}, {gg[2], 1, RealScalarList[[gg[0],2,2]]}], {gg[0], 1, SNumber[]}]})] 
				)
			],
			Ag[gauge_][a_, b_, c_, d_] :> Block[
				{ss1, ss2, ss3, ss4},
				Sum[
					Sum@@Join[
						{
							\[CapitalLambda][gauge][a, c, ss1/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2]] (
								\[CapitalLambda][gauge][ss1/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2], d] \[CapitalLambda][gauge][ss2/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], b, ss4/@Range[0,NumberOfSubgroups+2]] - 3 \[CapitalLambda][gauge][ss1/@Range[0,NumberOfSubgroups+2], ss3/@Range[0,NumberOfSubgroups+2], ss2/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2]] \[CapitalLambda][gauge][ss2/@Range[0,NumberOfSubgroups+2], ss4/@Range[0,NumberOfSubgroups+2], b, d]
							)//.sub\[CapitalLambda]S,
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
					],
					{ss1[0], 1, SNumber[]},
					{ss2[0], 1, SNumber[]},
					{ss3[0], 1, SNumber[]},
					{ss4[0], 1, SNumber[]}
				]
			]
		};
		
		
		(* Contraction of two scalar generators, see for instance arXiv:hep-ph/0211440 eq. (117) for Scalars and Fermions*)
		sub\[CapitalLambda]S := {
			(* For terms with two gauge groups *)
			\[CapitalLambda][gaug1_, gaug2_][a_, b_, c_, d_] :> If[
				gaug1 == gaug2, 
				\[CapitalLambda][gaug1][a, b, c, d]/.sub\[CapitalLambda]S,
				KroneckerDelta[a[[gaug2+3]], c[[gaug2+3]]] KroneckerDelta[b[[gaug2+3]], d[[gaug2+3]]] \[CapitalLambda][gaug1][ReplacePart[a, (gaug2+3)->1], ReplacePart[b, (gaug2+3)->1], ReplacePart[c, (gaug2+3)->1], ReplacePart[d, (gaug2+3)->1]]/.sub\[CapitalLambda]S
			],
			(** At least one is gauge singlet *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;(ListGauge[[gaug,3]] =!= 1 && (RealScalarList[[a[[1]],3,gaug]] == 1 || RealScalarList[[b[[1]],3,gaug]] == 1 || RealScalarList[[c[[1]],3,gaug]] == 1 || RealScalarList[[d[[1]],3,gaug]] == 1)),
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
				(KroneckerDelta[a[[gaug+3]],d[[gaug+3]]] KroneckerDelta[b[[gaug+3]],c[[gaug+3]]] - KroneckerDelta[a[[gaug+3]],b[[gaug+3]]] KroneckerDelta[c[[gaug+3]],d[[gaug+3]]]) TensorDelta[Delete[a,gaug+3], Delete[c,gaug+3]] TensorDelta[Delete[b,gaug+3], Delete[d,gaug+3]]
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
			\[CapitalLambda][gaug_][a_,b_, c_, d_] :>(\[CapitalLambda][ListGauge[[gaug,1]], RealScalarList[[a[[1]],1]], RealScalarList[[b[[1]],1]], RealScalarList[[c[[1]],1]], RealScalarList[[d[[1]],1]]][a[[2;;]], b[[2;;]], c[[2;;]], d[[2;;]]])
		};
		
		sub\[CapitalLambda]F := {
			(* For terms with two gauge groups *)
			\[CapitalLambda][gaug1_, gaug2_][a_, b_, c_, d_] :> If[
				gaug1 == gaug2, 
				\[CapitalLambda][gaug1][a, b, c, d]/.sub\[CapitalLambda]F,
				KroneckerDelta[a[[gaug2+2]], c[[gaug2+2]]] KroneckerDelta[b[[gaug2+2]], d[[gaug2+2]]] \[CapitalLambda][gaug1][ReplacePart[a, (gaug2+2)->1], ReplacePart[b, (gaug2+2)->1], ReplacePart[c, (gaug2+2)->1], ReplacePart[d, (gaug2+2)->1]]/.sub\[CapitalLambda]F
			],
			(** At least one is gauge singlet *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;(ListGauge[[gaug,3]] =!= 1 && (WeylFermionList[[a[[1]],3,gaug]] == 1 || WeylFermionList[[b[[1]],3,gaug]] == 1 || WeylFermionList[[c[[1]],3,gaug]] == 1 || WeylFermionList[[d[[1]],3,gaug]] == 1)),
			(** SU(N) -- all in fundamental representation *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (
				1/2(KroneckerDelta[a[[gaug+2]],d[[gaug+2]]] KroneckerDelta[b[[gaug+2]],c[[gaug+2]]]  - 1/ListGauge[[gaug,3]] KroneckerDelta[a[[gaug+2]],c[[gaug+2]]] KroneckerDelta[b[[gaug+2]],d[[gaug+2]]]) TensorDelta[Delete[a,gaug+2], Delete[c,gaug+2]] TensorDelta[Delete[b,gaug+2], Delete[d,gaug+2]]
			)/;(
				ListGauge[[gaug,2]] === SU && 
				WeylFermionList[[a[[1]], 3, gaug]] == ListGauge[[gaug,3]] && 
				WeylFermionList[[b[[1]], 3, gaug]] == ListGauge[[gaug,3]] && 
				WeylFermionList[[c[[1]], 3, gaug]] == ListGauge[[gaug,3]] && 
				WeylFermionList[[d[[1]], 3, gaug]] == ListGauge[[gaug,3]]
			),
			(** SO(N) -- all in fundamental representation *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (
				(KroneckerDelta[a[[gaug+2]],d[[gaug+2]]] KroneckerDelta[b[[gaug+2]],c[[gaug+2]]] - KroneckerDelta[a[[gaug+2]],b[[gaug+2]]] KroneckerDelta[c[[gaug+2]],d[[gaug+2]]]) TensorDelta[Delete[a,gaug+2], Delete[c,gaug+2]] TensorDelta[Delete[b,gaug+2], Delete[d,gaug+2]]
			)/;(
				ListGauge[[gaug,2]] === SO && 
				WeylFermionList[[a[[1]], 3, gaug]] == ListGauge[[gaug,3]] && 
				WeylFermionList[[b[[1]], 3, gaug]] == ListGauge[[gaug,3]] && 
				WeylFermionList[[c[[1]], 3, gaug]] == ListGauge[[gaug,3]] && 
				WeylFermionList[[d[[1]], 3, gaug]] == ListGauge[[gaug,3]]
			),
			(** U(1) *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :>(
					WeylFermionList[[a[[1]], 3, gaug]] WeylFermionList[[b[[1]], 3, gaug]] TensorDelta[a,c] TensorDelta[b,d]
			)/;(ListGauge[[gaug, 3]] === 1),
			(** unknown gauge group*)
			\[CapitalLambda][gaug_][a_,b_, c_, d_] :>(\[CapitalLambda][ListGauge[[gaug,1]], WeylFermionList[[a[[1]],1]], WeylFermionList[[b[[1]],1]], WeylFermionList[[c[[1]],1]], WeylFermionList[[d[[1]],1]]][a[[2;;]], b[[2;;]], c[[2;;]], d[[2;;]]])
		};
		
		sub\[CapitalLambda]SF := {
			(* For terms with two gauge groups *)
			\[CapitalLambda][gaug1_, gaug2_][a_, b_, c_, d_] :> If[
				gaug1 == gaug2, 
				\[CapitalLambda][gaug1][a, b, c, d]/.sub\[CapitalLambda]SF,
				KroneckerDelta[a[[gaug2+3]], c[[gaug2+3]]] KroneckerDelta[b[[gaug2+2]], d[[gaug2+2]]] \[CapitalLambda][gaug1][ReplacePart[a, (gaug2+3)->1], ReplacePart[b, (gaug2+2)->1], ReplacePart[c, (gaug2+3)->1], ReplacePart[d, (gaug2+2)->1]]/.sub\[CapitalLambda]SF
			],
			(** At least one is gauge singlet *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (0)/;(ListGauge[[gaug,3]] =!= 1 && (RealScalarList[[a[[1]],3,gaug]] == 1 || WeylFermionList[[b[[1]],3,gaug]] == 1 || RealScalarList[[c[[1]],3,gaug]] == 1 || WeylFermionList[[d[[1]],3,gaug]] == 1)),
			(** SU(N) -- all in fundamental representation *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (
				If[
					(a[[1]] == c[[1]])
					,
					1/4 (KroneckerDelta[a[[gaug+3]],d[[gaug+2]]] KroneckerDelta[b[[gaug+2]],c[[gaug+3]]]  - KroneckerDelta[a[[gaug+3]],b[[gaug+2]]] KroneckerDelta[c[[gaug+3]],d[[gaug+2]]]) TensorDelta[Delete[a,gaug+3][[2;;]], Delete[c,gaug+3][[2;;]]] TensorDelta[Delete[b,gaug+2][[2;;]], Delete[d,gaug+2][[2;;]]] KroneckerDelta[b[[1]], d[[1]]]
					,
					0
				] + If[
						(RealScalarList[[a[[1]], 1]][[1]] === RealScalarList[[c[[1]], 1]][[1]] &&
						RealScalarList[[a[[1]], 1]][[0]] =!= RealScalarList[[c[[1]], 1]][[0]] &&
						RealScalarList[[a[[1]], 1]][[0]] === Re && RealScalarList[[c[[1]], 1]][[0]] === Im),
						+I/4(KroneckerDelta[a[[gaug+3]],d[[gaug+2]]] KroneckerDelta[b[[gaug+2]],c[[gaug+3]]] + KroneckerDelta[a[[gaug+3]],b[[gaug+2]]] KroneckerDelta[c[[gaug+3]],d[[gaug+2]]] - 2/ListGauge[[gaug,3]] KroneckerDelta[a[[gaug+3]],c[[gaug+3]]] KroneckerDelta[b[[gaug+2]],d[[gaug+2]]]) TensorDelta[Delete[a,gaug+3][[2;;]], Delete[c,gaug+3][[2;;]]] TensorDelta[Delete[b,gaug+2], Delete[d,gaug+2]]
						 ,
						0
					] + If[
							(RealScalarList[[a[[1]], 1]][[1]] === RealScalarList[[c[[1]], 1]][[1]] &&
							RealScalarList[[a[[1]], 1]][[0]] =!= RealScalarList[[c[[1]], 1]][[0]] &&
							RealScalarList[[a[[1]], 1]][[0]] === Im && RealScalarList[[c[[1]], 1]][[0]] === Re),
							-I/4(KroneckerDelta[a[[gaug+3]],d[[gaug+2]]] KroneckerDelta[b[[gaug+2]],c[[gaug+3]]] + KroneckerDelta[a[[gaug+3]],b[[gaug+2]]] KroneckerDelta[c[[gaug+3]],d[[gaug+2]]] - 2/ListGauge[[gaug,3]] KroneckerDelta[a[[gaug+3]],c[[gaug+3]]] KroneckerDelta[b[[gaug+2]],d[[gaug+2]]]) TensorDelta[Delete[a,gaug+3][[2;;]], Delete[c,gaug+3][[2;;]]] TensorDelta[Delete[b,gaug+2], Delete[d,gaug+2]]
							,
							0
						]
			)/;(
				ListGauge[[gaug,2]] === SU && 
				RealScalarList[[a[[1]], 3, gaug]] == ListGauge[[gaug,3]] && 
				WeylFermionList[[b[[1]], 3, gaug]] == ListGauge[[gaug,3]] && 
				RealScalarList[[c[[1]], 3, gaug]] == ListGauge[[gaug,3]] && 
				WeylFermionList[[d[[1]], 3, gaug]] == ListGauge[[gaug,3]]
			),
			(** SO(N) -- all in fundamental representation *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :> (
				(KroneckerDelta[a[[gaug+2]],d[[gaug+2]]] KroneckerDelta[b[[gaug+2]],c[[gaug+2]]] - KroneckerDelta[a[[gaug+2]],b[[gaug+2]]] KroneckerDelta[c[[gaug+2]],d[[gaug+2]]]) TensorDelta[Delete[a,gaug+2], Delete[c,gaug+2]] TensorDelta[Delete[b,gaug+2], Delete[d,gaug+2]]
			)/;(
				ListGauge[[gaug,2]] === SO && 
				RealScalarList[[a[[1]], 3, gaug]] == ListGauge[[gaug,3]] && 
				WeylFermionList[[b[[1]], 3, gaug]] == ListGauge[[gaug,3]] && 
				RealScalarList[[c[[1]], 3, gaug]] == ListGauge[[gaug,3]] && 
				WeylFermionList[[d[[1]], 3, gaug]] == ListGauge[[gaug,3]]
			),
			(** U(1) *)
			\[CapitalLambda][gaug_][a_, b_, c_, d_] :>(
				(
					RealScalarList[[a[[1]],3,gaug]] WeylFermionList[[b[[1]],3,gaug]] 
					ComplexDelta[RealScalarList[[a[[1]],1]], RealScalarList[[c[[1]],1]]]
					(If[RealScalarList[[a[[1]],1]][[0]] === Re &&  RealScalarList[[c[[1]],1]][[0]] === Im, +I ,
						If[RealScalarList[[a[[1]],1]][[0]] === Im &&  RealScalarList[[c[[1]],1]][[0]] === Re, -I , 0]
					])
					TensorDelta[a[[2;;]],c[[2;;]]] TensorDelta[b,d]
				)
			)/;(ListGauge[[gaug, 3]] === 1),
			(** unknown gauge group*)
			\[CapitalLambda][gaug_][a_,b_, c_, d_] :>(\[CapitalLambda][ListGauge[[gaug,1]], RealScalarList[[a[[1]],1]], WeylFermionList[[b[[1]],1]], RealScalarList[[c[[1]],1]], WeylFermionList[[d[[1]],1]]][a[[2;;]], b[[2;;]], c[[2;;]], d[[2;;]]])
		};
		
		
		(* sum over all fermions / scalars *)
		FSum[a___] := ReleaseHold[If[WeylFermionList == {}, 0, Sum[(a)&[sumindex], {sumindex,1,FNumber[]}]]];
		SSum[a___] := ReleaseHold[If[RealScalarList == {}, 0, Sum[(a)&[sumindex], {sumindex,1,SNumber[]}]]];

		
		(* overall multiplicity of particles / gauges *)
		FMultiplicity[f_] := WeylFermionList[[f,2]] Times@@(Function[{x},If[ListGauge[[x,3]]===1, 1, WeylFermionList[[f,3,x]]]]/@Range[NumberOfSubgroups]);
		SMultiplicity[s_] := RealScalarList[[s,2,1]] RealScalarList[[s,2,2]] Times@@(Function[{x},If[ListGauge[[x,3]]===1, 1, RealScalarList[[s,3,x]]]]/@Range[NumberOfSubgroups]);
		FMultiplicity[f_, g_] := If[ListGauge[[g,3]]===1, 1, WeylFermionList[[f,3,g]]];
		SMultiplicity[s_, g_] := If[ListGauge[[g,3]]===1, 1, RealScalarList[[s,3,g]]];
		
		(* Generation contraction for Yukawa products and traces *)
		GetGenProd[symList_, sVarList_, i_, j_] := Module[
			{split, sumInd},
			If[
				symList == {} || sVarList == {} || Dimensions[symList][[1]] <= 0, 
				Return[0];
			];
			For[split=1, split<=Dimensions[symList][[1]], split++,
				If[
					!(MatchQ[symList[[split, 1, 2]], Mat[___]] || MatchQ[symList[[split, 1, 2]], Conjugate[Mat[___]]] || MatchQ[symList[[split, 1, 2]], a_ Mat[___]] || MatchQ[symList[[split, 1, 2]], a_ Conjugate[Mat[___]]]  || MatchQ[symList[[split, 1, 2]], Mat[___]&] || MatchQ[symList[[split, 1, 2]], Conjugate[Mat[___]]&]  || MatchQ[symList[[split, 1, 2]], a_ Mat[___]&] || MatchQ[symList[[split, 1, 2]], a_ Conjugate[Mat[___]]&]),
					Return[
						If[(split == Dimensions[symList][[1]]),
							If[split == 1, 1, ((prod@@symList[[;;split-1, 1, 1]])[i,j]/.{prod[C2[aa___]][i1_,i2_] :> KroneckerDelta[i1,i2] C2[aa], prod[A___, C2[aa___], B___][C___] :> C2[aa] prod[A,B][C]}) Refine[Times@@(Function[{x},x[1]]/@symList[[;;split-1, 1, 2]]//.Mat:>Identity)]] symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], i, j],
							Sum[
								If[split == 1, 1, ((prod@@symList[[;;split-1, 1, 1]])[i,sumInd]/.{prod[C2[aa___]][i1_,i2_] :> KroneckerDelta[i1,i2] C2[aa], prod[A___, C2[aa___], B___][C___] :> C2[aa] prod[A,B][C]}) Refine[Times@@(Function[{x},x[1]]/@symList[[;;split-1, 1, 2]]//.Mat:>Identity)]] symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], i, sumInd] GetGenProd[symList[[split+1;;]], sVarList[[split+1;;]], sumInd, j],
								{sumInd, 1, symList[[split, 1, 6]]}
							]
						]
					];
				];
				If[split==Dimensions[symList][[1]], Break[];];
			];
			Return[((prod@@(symList[[All, 1, 1]]))[i,j] /.{prod[C2[aa___]][i1_,i2_] :> KroneckerDelta[i1,i2] C2[aa], prod[A___, C2[aa___], B___][C___] :> C2[aa] prod[A,B][C]}) Refine[Times@@(Function[{x},x[1]]/@symList[[All, 1, 2]]//.Mat:>Identity)]];
		];
		
		GetGenTrace[symList_, sVarList_] := Module[
			{split, sumInd1, sumInd2, sumInd3},
			If[
				symList == {} || sVarList == {} || Dimensions[symList][[1]] <= 0, 
				Return[0];
			];
			For[split=1, split<=Dimensions[symList][[1]], split++,
				If[
					!(MatchQ[symList[[split, 1, 2]], Mat[___]] || MatchQ[symList[[split, 1, 2]], Conjugate[Mat[___]]] || MatchQ[symList[[split, 1, 2]], a_ Mat[___]] || MatchQ[symList[[split, 1, 2]], a_ Conjugate[Mat[___]]]  || MatchQ[symList[[split, 1, 2]], Mat[___]&] || MatchQ[symList[[split, 1, 2]], Conjugate[Mat[___]]&]  || MatchQ[symList[[split, 1, 2]], a_ Mat[___]&] || MatchQ[symList[[split, 1, 2]], a_ Conjugate[Mat[___]]&]),
					Return[
						If[split != Dimensions[symList][[1]],
							If[split == 1,
								Sum[
									symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], sumInd2, sumInd3] GetGenProd[symList[[split+1;;]], sVarList[[split+1;;]], sumInd3, sumInd2],
									{sumInd2, 1, symList[[split,1,5]]},
									{sumInd3, 1, symList[[split,1,6]]}
								],
								Sum[
									((prod@@symList[[;;split-1, 1, 1]])[sumInd1,sumInd2] /.{prod[C2[aa___]][i1_,i2_] :> KroneckerDelta[i1,i2] C2[aa], prod[A___, C2[aa___], B___][C___] :> C2[aa] prod[A,B][C]}) Refine[Times@@(Function[{x},x[1]]/@symList[[;;split-1, 1, 2]]//.Mat:>Identity)] symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], sumInd2, sumInd3] GetGenProd[symList[[split+1;;]], sVarList[[split+1;;]], sumInd3, sumInd1],
									{sumInd1, 1, symList[[1,1,4]]},
									{sumInd2, 1, symList[[split,1,5]]},
									{sumInd3, 1, symList[[split,1,6]]}
								]
							],
							If[split == 1,
								Sum[
									symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], sumInd1, sumInd1],
									{sumInd1, 1, symList[[split,1,5]]}
								],
								Sum[
									((prod@@symList[[;;split-1, 1, 1]])[sumInd1,sumInd2]/.{prod[C2[aa___]][i1_,i2_] :> KroneckerDelta[i1,i2] C2[aa], prod[A___, C2[aa___], B___][C___] :> C2[aa] prod[A,B][C]}) Refine[Times@@(Function[{x},x[1]]/@symList[[;;split-1, 1, 2]]//.Mat:>Identity)] symList[[split, 1, 1]] symList[[split, 1, 2]][sVarList[[split,1]], sVarList[[split,2]], sumInd2, sumInd1],
									{sumInd1, 1, symList[[1,1,5]]},
									{sumInd2, 1, symList[[split,1,5]]}
								]
							]
						]
					];
				];
				If[split==Dimensions[symList][[1]], Break[];];
			];
			Return[(tr@@(symList[[All, 1, 1]])/.{tr[C2[aa_, bb_]]:>WeylFermionList[[aa,2]] C2[aa,bb], tr[AA___, C2[aa___], BB___]:>C2[aa] tr[AA,BB]}) Refine[Times@@(Function[{x},x[1]]/@symList[[All, 1, 2]]//.Mat:>Identity)]];
		];
		
		(* helper function to separate matrices and contractions in fermion generations from Yukawa products *)
		Mat[A_][___] := Mat[A];
		
		
		(* optimized functions for Yukawa traces *)
		SolveTrace2Fast[Y1_, Y2_, SIdx_] := Block[
			{sumInd1,sumInd2},
			ReleaseHold[SolveTrace[Y1,Y2] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]//.subYuk /.{
				tr[y1_, y2_]:>Times@@Join[
					{
						Refine[
							GetGenTrace[{y1, y2}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}}]//.subProd
						]
					},
					((Function[{x}, Refine[Sum[
						y1[[x+1,1]][SIdx[[x+1,1]], sumInd1[x], sumInd2[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd2[x], sumInd1[x]], 
						{sumInd1[x], 1, y1[[x+1, 3]]},
						{sumInd2[x], 1, y1[[x+1, 4]]}
					]]]) /@ Range[NumberOfSubgroups])
				]
			}
		];
		
		SolveTrace3Fast[Y1_, Y2_, Y3_, SIdx_] := Block[
			{sumInd1,sumInd2,sumInd3},
			ReleaseHold[SolveTrace[Y1,Y2,Y3] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]//.subYuk /.{
				tr[y1_, y2_, y3_]:>Times@@Join[
					{
						Refine[
							GetGenTrace[{y1, y2, y3}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}}]//.subProd
						]
					},
					((Function[{x}, Refine[Sum[
						 y1[[x+1,1]][SIdx[[x+1,1]], sumInd1[x], sumInd2[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd2[x], sumInd3[x]]  y3[[x+1, 1]][SIdx[[x+1,3]], sumInd3[x], sumInd1[x]], 
						{sumInd1[x], 1, y1[[x+1, 3]]},
						{sumInd2[x], 1, y1[[x+1, 4]]},
						{sumInd3[x], 1, y3[[x+1, 3]]}
					]]]) /@ Range[NumberOfSubgroups])
				]
			}
		];
		
		SolveTrace4Fast[Y1_, Y2_, Y3_, Y4_, SIdx_] := Block[
			{sumInd1,sumInd2,sumInd3, sumInd4},
			ReleaseHold[SolveTrace[Y1,Y2,Y3,Y4] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]//.subYuk /.{
				tr[y1_, y2_, y3_, y4_]:>Times@@Join[
					{
						Refine[
							GetGenTrace[{y1, y2, y3, y4}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}, {SIdx[[1,7]], SIdx[[1,8]]}}]//.subProd
						]
					},
					((Function[{x}, Refine[Sum[
						 y1[[x+1,1]][SIdx[[x+1,1]], sumInd1[x], sumInd2[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd2[x], sumInd3[x]]  y3[[x+1,1]][SIdx[[x+1,3]], sumInd3[x], sumInd4[x]] y4[[x+1,1]][SIdx[[x+1,4]], sumInd4[x], sumInd1[x]], 
						{sumInd1[x], 1, y1[[x+1, 3]]},
						{sumInd2[x], 1, y1[[x+1, 4]]},
						{sumInd3[x], 1, y3[[x+1, 3]]},
						{sumInd4[x], 1, y3[[x+1, 4]]}
					]]]) /@ Range[NumberOfSubgroups])
				]
			}
		];
		
		SolveTrace5Fast[Y1_, Y2_, Y3_, Y4_, Y5_, SIdx_] := Block[
			{sumInd1,sumInd2,sumInd3, sumInd4, sumInd5},
			ReleaseHold[SolveTrace[Y1,Y2,Y3,Y4,Y5] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]//.subYuk /.{
				tr[y1_, y2_, y3_, y4_, y5_]:>Times@@Join[
					{
						Refine[
							GetGenTrace[{y1, y2, y3, y4, y5}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}, {SIdx[[1,7]], SIdx[[1,8]]}, {SIdx[[1,9]], SIdx[[1,10]]}}]//.subProd
						]
					},
					((Function[{x}, Refine[Sum[
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
		
		SolveTrace6Fast[Y1_, Y2_, Y3_, Y4_, Y5_, Y6_, SIdx_] := Block[
			{sumInd1,sumInd2,sumInd3, sumInd4, sumInd5, sumInd6},
			ReleaseHold[SolveTrace[Y1,Y2,Y3,Y4,Y5,Y6] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]//.subYuk /.{
				tr[y1_, y2_, y3_, y4_, y5_, y6_]:>Times@@Join[
					{
						Refine[
							GetGenTrace[{y1, y2, y3, y4, y5, y6}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}, {SIdx[[1,7]], SIdx[[1,8]]}, {SIdx[[1,9]], SIdx[[1,10]]}, {SIdx[[1,11]], SIdx[[1,12]]}}]//.subProd
						]
					},
					((Function[{x}, Refine[Sum[
						 y1[[x+1,1]][SIdx[[x+1,1]], sumInd1[x], sumInd2[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd2[x], sumInd3[x]]  y3[[x+1,1]][SIdx[[x+1,3]], sumInd3[x], sumInd4[x]] y4[[x+1,1]][SIdx[[x+1,4]], sumInd4[x], sumInd5[x]] y5[[x+1,1]][SIdx[[x+1,5]], sumInd5[x], sumInd6[x]] y6[[x+1,1]][SIdx[[x+1,6]], sumInd6[x], sumInd1[x]], 
						{sumInd1[x], 1, y1[[x+1, 3]]},
						{sumInd2[x], 1, y1[[x+1, 4]]},
						{sumInd3[x], 1, y3[[x+1, 3]]},
						{sumInd4[x], 1, y3[[x+1, 4]]},
						{sumInd5[x], 1, y5[[x+1, 3]]},
						{sumInd5[x], 1, y5[[x+1, 4]]}
					]]]) /@ Range[NumberOfSubgroups])
				]
			}
		];
		
		SolveProd2Fast[Y1_, Y2_, li_, lj_, SIdx_] := Block[
			{sumInd1},
			ReleaseHold[SolveProd[Y1, Y2, li[[1]], lj[[1]]] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]//.subYuk /.{
				prod[y1_, y2_]:>Times@@Join[
					{
						Refine[
							GetGenProd[{y1, y2}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}}, li[[2]], lj[[2]]]//.subProd
						]
					},
					(
						Function[{x}, Refine[Sum[
							y1[[x+1,1]][SIdx[[x+1,1]], li[[2+x]], sumInd1[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd1[x], lj[[2+x]]],
							{sumInd1[x], 1, y2[[x+1,3]]}
						]]]/@Range[NumberOfSubgroups]
					)
				]
			}
		];
		
		SolveProd3Fast[Y1_, Y2_, Y3_, li_, lj_, SIdx_] := Block[
			{sumInd1, sumInd2},
			ReleaseHold[SolveProd[Y1, Y2, Y3, li[[1]], lj[[1]]] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]//.subYuk /.{
				prod[y1_, y2_, y3_]:>Times@@Join[
					{
						Refine[
							GetGenProd[{y1, y2, y3}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}}, li[[2]], lj[[2]]]//.subProd
						]
					},
					(
						Function[{x}, Refine[Sum[
							y1[[x+1,1]][SIdx[[x+1,1]], li[[2+x]], sumInd1[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd1[x], sumInd2[x]] y3[[x+1,1]][SIdx[[x+1,3]], sumInd2[x], lj[[2+x]]],
							{sumInd1[x], 1, y2[[x+1,3]]},
							{sumInd2[x], 1, y2[[x+1,4]]}
						]]]/@Range[NumberOfSubgroups]
					)
				]
			}
		];
		
		SolveProd4Fast[Y1_, Y2_, Y3_, Y4_, li_, lj_, SIdx_] := Block[
			{sumInd1, sumInd2, sumInd3},
			ReleaseHold[SolveProd[Y1, Y2, Y3, Y4, li[[1]], lj[[1]]] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]//.subYuk /.{
				prod[y1_, y2_, y3_, y4_]:>Times@@Join[
					{
						Refine[
							GetGenProd[{y1, y2, y3, y4}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}, {SIdx[[1,7]],SIdx[[1,8]]}}, li[[2]], lj[[2]]]//.subProd
						]
					},
					(
						Function[{x}, Refine[Sum[
							y1[[x+1,1]][SIdx[[x+1,1]], li[[2+x]], sumInd1[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd1[x], sumInd2[x]] y3[[x+1,1]][SIdx[[x+1,3]], sumInd2[x], sumInd3[x]] y4[[x+1,4]][SIdx[[x+1,4]], sumInd3[x], lj[[2+x]]],
							{sumInd1[x], 1, y2[[x+1,3]]},
							{sumInd2[x], 1, y2[[x+1,4]]},
							{sumInd3[x], 1, y4[[x+1,3]]}
						]]]/@Range[NumberOfSubgroups]
					)
				]
			}
		];
		
		SolveProd5Fast[Y1_, Y2_, Y3_, Y4_, Y5_, li_, lj_, SIdx_] := Block[
			{sumInd1, sumInd2, sumInd3, sumInd4},
			ReleaseHold[SolveProd[Y1, Y2, Y3, Y4, Y5, li[[1]], lj[[1]]] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]//.subYuk /.{
				prod[y1_, y2_, y3_, y4_]:>Times@@Join[
					{
						Refine[
							GetGenProd[{y1, y2, y3, y4, y5}, {{SIdx[[1,1]],SIdx[[1,2]]}, {SIdx[[1,3]],SIdx[[1,4]]}, {SIdx[[1,5]],SIdx[[1,6]]}, {SIdx[[1,7]],SIdx[[1,8]]}, {SIdx[[1,9]], SIdx[[1,10]]}}, li[[2]], lj[[2]]]//.subProd
						]
					},
					(
						Function[{x}, Refine[Sum[
							y1[[x+1,1]][SIdx[[x+1,1]], li[[2+x]], sumInd1[x]] y2[[x+1,1]][SIdx[[x+1,2]], sumInd1[x], sumInd2[x]] y3[[x+1,1]][SIdx[[x+1,3]], sumInd2[x], sumInd3[x]] y4[[x+1,4]][SIdx[[x+1,4]], sumInd3[x], sumInd4[x]] y5[[x+1,1]][SIdx[[x+1,5]] sumInd4[x], lj[[2+x]]],
							{sumInd1[x], 1, y2[[x+1,3]]},
							{sumInd2[x], 1, y2[[x+1,4]]},
							{sumInd3[x], 1, y4[[x+1,3]]},
							{sumInd4[x], 1, y4[[x+1,4]]}
						]]]/@Range[NumberOfSubgroups]
					)
				]
			}
		];
		
		SolveSProd2Fast[L1_, L2_, SIdx_] := Block[
			{},
			ReleaseHold[prod[L1, L2]/.subQuart//.subProd]//.subQuart/.{
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
		
		SolveSProd3Fast[L1_, L2_, L3_, SIdx_] := Block[
			{},
			ReleaseHold[prod[L1, L2, L3]/.subQuart//.subProd]//.subQuart/.{
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
		
		
		
		(* Yukawa trace and products of gauge and generation indices *)
		SolveTrace2[y1_, y2_, ScGauge_] := Join[
			{
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx12,scGenIdx2,scGenIdx22] GetGenTrace[{y1, y2}, {{scGenIdx1,scGenIdx12}, {scGenIdx2,scGenIdx22}}]//.subProd,
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx12, 1, y1[[1,4]]},
					{scGenIdx22, 1, y2[[1,4]]}
				]]
			},
			((Function[{x}, Refine[Sum[
				ScGauge[[x+1]][scGaugeIdx1[x], scGaugeIdx2[x]] y1[[x + 1, 1]][scGaugeIdx1[x], sumInd1[x], sumInd2[x]] y2[[x + 1, 1]][scGaugeIdx2[x], sumInd2[x], sumInd1[x]], 
				{sumInd1[x], 1, y1[[x+1, 3]]},
				{sumInd2[x], 1, y1[[x+1, 4]]},
				{scGaugeIdx1[x], 1, y1[[x+1, 2]]},
				{scGaugeIdx2[x], 1, y2[[x+1, 2]]}
			]]]) /@ Range[NumberOfSubgroups])
		];
		
		SolveTrace3[y1_, y2_, y3_, ScGauge_] := Join[
			{ 
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx12,scGenIdx2,scGenIdx22,scGenIdx3,scGenIdx32] GetGenTrace[{y1, y2, y3}, {{scGenIdx1,scGenIdx12}, {scGenIdx2,scGenIdx22}, {scGenIdx3,scGenIdx32}}]//.subProd,
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx3, 1, y3[[1,3]]},
					{scGenIdx12, 1, y1[[1,4]]},
					{scGenIdx22, 1, y2[[1,4]]},
					{scGenIdx32, 1, y3[[1,4]]}
				]]
			},
			((Function[{x}, Refine[
				Sum[ScGauge[[x+1]][scGaugeIdx1[x], scGaugeIdx2[x], scGaugeIdx3[x]] y1[[x+1, 1]][scGaugeIdx1[x], sumInd1[x], sumInd2[x]] y2[[x+1, 1]][scGaugeIdx2[x], sumInd2[x], sumInd3[x]]  y3[[x+1, 1]][scGaugeIdx3[x], sumInd3[x], sumInd1[x]], 
					{sumInd1[x], 1, y1[[x+1, 3]]}, 
					{sumInd2[x], 1, y1[[x+1, 4]]},
					{sumInd3[x], 1, y3[[x+1, 3]]},
					{scGaugeIdx1[x], 1, y1[[x+1, 2]]},
					{scGaugeIdx2[x], 1, y2[[x+1, 2]]},
					{scGaugeIdx3[x], 1, y3[[x+1, 2]]}
				]
			]]) /@ Range[NumberOfSubgroups])
		];
		
		SolveTrace4[y1_, y2_, y3_, y4_, ScGauge_] := Join[
			{
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx12,scGenIdx2,scGenIdx22,scGenIdx3,scGenIdx32,scGenIdx4,scGenIdx42] GetGenTrace[{y1, y2, y3, y4}, {{scGenIdx1,scGenIdx12}, {scGenIdx2,scGenIdx22}, {scGenIdx3,scGenIdx32}, {scGenIdx4,scGenIdx42}}]//.subProd,
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx3, 1, y3[[1,3]]},
					{scGenIdx4, 1, y4[[1,3]]},
					{scGenIdx12, 1, y1[[1,4]]},
					{scGenIdx22, 1, y2[[1,4]]},
					{scGenIdx32, 1, y3[[1,4]]},
					{scGenIdx42, 1, y4[[1,4]]}
				]]
			},
			((Function[{x}, Refine[
				Sum[ScGauge[[x+1]][scGaugeIdx1[x], scGaugeIdx2[x], scGaugeIdx3[x], scGaugeIdx4[x]] y1[[x+1, 1]][scGaugeIdx1[x], sumInd1[x], sumInd2[x]] y2[[x+1, 1]][scGaugeIdx2[x], sumInd2[x], sumInd3[x]] y3[[x+1, 1]][scGaugeIdx3[x], sumInd3[x], sumInd4[x]] y4[[x+1, 1]][scGaugeIdx4[x], sumInd4[x], sumInd1[x]], 
					{sumInd1[x], 1, y1[[x+1, 3]]}, 
					{sumInd2[x], 1, y1[[x+1, 4]]},
					{sumInd3[x], 1, y3[[x+1, 3]]},
					{sumInd4[x], 1, y3[[x+1, 4]]},
					{scGaugeIdx1[x], 1, y1[[x+1, 2]]},
					{scGaugeIdx2[x], 1, y2[[x+1, 2]]},
					{scGaugeIdx3[x], 1, y3[[x+1, 2]]},
					{scGaugeIdx4[x], 1, y4[[x+1, 2]]}
				]
			]]) /@ Range[NumberOfSubgroups])
		];
		
		SolveTrace5[y1_, y2_, y3_, y4_, y5_, ScGauge_] := Join[
			{
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx12,scGenIdx2,scGenIdx22,scGenIdx3,scGenIdx32,scGenIdx4,scGenIdx42,scGenIdx5,scGenIdx52] GetGenTrace[{y1, y2, y3, y4, y5}, {{scGenIdx1,scGenIdx12}, {scGenIdx2,scGenIdx22}, {scGenIdx3,scGenIdx32}, {scGenIdx4,scGenIdx42}, {scGenIdx5,scGenIdx52}}]//.subProd,
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx3, 1, y3[[1,3]]},
					{scGenIdx4, 1, y4[[1,3]]},
					{scGenIdx5, 1, y5[[1,3]]},
					{scGenIdx12, 1, y1[[1,4]]},
					{scGenIdx22, 1, y2[[1,4]]},
					{scGenIdx32, 1, y3[[1,4]]},
					{scGenIdx42, 1, y4[[1,4]]},
					{scGenIdx52, 1, y5[[1,4]]}
				]]
			},
			((Function[{x}, Refine[
				Sum[ScGauge[[x+1]][scGaugeIdx1[x], scGaugeIdx2[x], scGaugeIdx3[x], scGaugeIdx4[x], scGaugeIdx5[x]] y1[[x+1, 1]][scGaugeIdx1[x], sumInd1[x], sumInd2[x]] y2[[x+1, 1]][scGaugeIdx2[x], sumInd2[x], sumInd3[x]] y3[[x+1, 1]][scGaugeIdx3[x], sumInd3[x], sumInd4[x]] y4[[x+1, 1]][scGaugeIdx4[x], sumInd4[x], sumInd5[x]] y5[[x+1, 1]][scGaugeIdx5[x], sumInd5[x], sumInd1[x]], 
					{sumInd1[x], 1, y1[[x+1, 3]]}, 
					{sumInd2[x], 1, y1[[x+1, 4]]},
					{sumInd3[x], 1, y3[[x+1, 3]]},
					{sumInd4[x], 1, y3[[x+1, 4]]},
					{sumInd5[x], 1, y5[[x+1, 3]]},
					{scGaugeIdx1[x], 1, y1[[x+1, 2]]},
					{scGaugeIdx2[x], 1, y2[[x+1, 2]]},
					{scGaugeIdx3[x], 1, y3[[x+1, 2]]},
					{scGaugeIdx4[x], 1, y4[[x+1, 2]]},
					{scGaugeIdx5[x], 1, y5[[x+1, 2]]}
				]
			]]) /@ Range[NumberOfSubgroups])
		];
		
			SolveTrace6[y1_, y2_, y3_, y4_, y5_, y6_, ScGauge_] := Join[
			{
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx12,scGenIdx2,scGenIdx22,scGenIdx3,scGenIdx32,scGenIdx4,scGenIdx42,scGenIdx5,scGenIdx52,scGenIdx6,scGenIdx62] GetGenTrace[{y1, y2, y3, y4, y5, y6}, {{scGenIdx1,scGenIdx12}, {scGenIdx2,scGenIdx22}, {scGenIdx3,scGenIdx32}, {scGenIdx4,scGenIdx42}, {scGenIdx5,scGenIdx52}, {scGenIdx6,scGenIdx62}}]//.subProd,
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx3, 1, y3[[1,3]]},
					{scGenIdx4, 1, y4[[1,3]]},
					{scGenIdx5, 1, y5[[1,3]]},
					{scGenIdx6, 1, y6[[1,3]]},
					{scGenIdx12, 1, y1[[1,4]]},
					{scGenIdx22, 1, y2[[1,4]]},
					{scGenIdx32, 1, y3[[1,4]]},
					{scGenIdx42, 1, y4[[1,4]]},
					{scGenIdx52, 1, y5[[1,4]]},
					{scGenIdx62, 1, y6[[1,4]]}
				]]
			},
			((Function[{x}, Refine[
				Sum[ScGauge[[x+1]][scGaugeIdx1[x], scGaugeIdx2[x], scGaugeIdx3[x], scGaugeIdx4[x], scGaugeIdx5[x], scGaugeIdx6[x]] y1[[x+1, 1]][scGaugeIdx1[x], sumInd1[x], sumInd2[x]] y2[[x+1, 1]][scGaugeIdx2[x], sumInd2[x], sumInd3[x]] y3[[x+1, 1]][scGaugeIdx3[x], sumInd3[x], sumInd4[x]] y4[[x+1, 1]][scGaugeIdx4[x], sumInd4[x], sumInd5[x]] y5[[x+1, 1]][scGaugeIdx5[x], sumInd5[x], sumInd6[x]] y6[[x+1, 1]][scGaugeIdx6[x], sumInd6[x], sumInd1[x]], 
					{sumInd1[x], 1, y1[[x+1, 3]]}, 
					{sumInd2[x], 1, y1[[x+1, 4]]},
					{sumInd3[x], 1, y3[[x+1, 3]]},
					{sumInd4[x], 1, y3[[x+1, 4]]},
					{sumInd5[x], 1, y5[[x+1, 3]]},
					{sumInd6[x], 1, y5[[x+1, 4]]},
					{scGaugeIdx1[x], 1, y1[[x+1, 2]]},
					{scGaugeIdx2[x], 1, y2[[x+1, 2]]},
					{scGaugeIdx3[x], 1, y3[[x+1, 2]]},
					{scGaugeIdx4[x], 1, y4[[x+1, 2]]},
					{scGaugeIdx5[x], 1, y5[[x+1, 2]]},
					{scGaugeIdx6[x], 1, y6[[x+1, 2]]}
				]
			]]) /@ Range[NumberOfSubgroups])
		];
		
		SolveProd2[y1_, y2_, Ll_, Lr_, ScGauge_] := Join[
			{ 
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx12,scGenIdx2,scGenIdx22] GetGenProd[{y1, y2}, {{scGenIdx1,scGenIdx12}, {scGenIdx2,scGenIdx22}}, Ll[[1]], Lr[[1]]] //.subProd,
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx12, 1, y1[[1,4]]},
					{scGenIdx22, 1, y2[[1,4]]}
				]]
			},
			(Function[{x},Refine[Sum[
				ScGauge[[x+1]][scGaugeIdx1[x], scGaugeIdx2[x]] y1[[x+1, 1]][scGaugeIdx1[x], Ll[[x+1]], sumInd1[x]] y2[[x+1, 1]][scGaugeIdx2[x], sumInd1[x], Lr[[x+1]]],
				{sumInd1[x], 1, y2[[x+1, 3]]},
				{scGaugeIdx1[x], 1, y1[[x+1, 2]]},
				{scGaugeIdx2[x], 1, y2[[x+1, 2]]}
			]]]/@Range[NumberOfSubgroups])
		];
		
		SolveProd3[y1_, y2_, y3_, Ll_, Lr_, ScGauge_] := Join[
			{
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx12,scGenIdx2,scGenIdx22,scGenIdx3,scGenIdx32]  GetGenProd[{y1, y2, y3}, {{scGenIdx1,scGenIdx12}, {scGenIdx2,scGenIdx22}, {scGenIdx3,scGenIdx32}}, Ll[[1]], Lr[[1]]] //.subProd,
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx3, 1, y3[[1,3]]},
					{scGenIdx12, 1, y1[[1,4]]},
					{scGenIdx22, 1, y2[[1,4]]},
					{scGenIdx32, 1, y3[[1,4]]}
				]]
			},
			(Function[{x},Refine[Sum[
				ScGauge[[x+1]][scGaugeIdx1[x], scGaugeIdx2[x], scGaugeIdx3[x]] y1[[x+1, 1]][scGaugeIdx1[x], Ll[[x+1]], sumInd1[x]] y2[[x+1, 1]][scGaugeIdx2[x], sumInd1[x],sumInd2[x]] y3[[x+1, 1]][scGaugeIdx3[x], sumInd2[x],Lr[[x+1]]],
				{sumInd1[x], 1, y2[[x+1, 3]]},
				{sumInd2[x], 1, y2[[x+1, 4]]},
				{scGaugeIdx1[x], 1, y1[[x+1, 2]]},
				{scGaugeIdx2[x], 1, y2[[x+1, 2]]},
				{scGaugeIdx3[x], 1, y3[[x+1, 2]]}
			]]]/@Range[NumberOfSubgroups])
		];
		
		SolveProd4[y1_, y2_, y3_, y4_, Ll_, Lr_, ScGauge_] := Join[
			{
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx12,scGenIdx2,scGenIdx22,scGenIdx3,scGenIdx32,scGenIdx4,scGenIdx42] GetGenProd[{y1, y2, y3, y4}, {{scGenIdx1,scGenIdx12}, {scGenIdx2,scGenIdx22}, {scGenIdx3,scGenIdx32}, {scGenIdx4,scGenIdx42}}, Ll[[1]], Lr[[1]]] //.subProd,
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx3, 1, y3[[1,3]]},
					{scGenIdx4, 1, y4[[1,3]]},
					{scGenIdx12, 1, y1[[1,4]]},
					{scGenIdx22, 1, y2[[1,4]]},
					{scGenIdx32, 1, y3[[1,4]]},
					{scGenIdx42, 1, y4[[1,4]]}
				]]
			},
			(Function[{x},Refine[Sum[
				ScGauge[[x+1]][scGaugeIdx1[x], scGaugeIdx2[x], scGaugeIdx3[x], scGaugeIdx4[x]] y1[[x+1, 1]][scGaugeIdx1[x], Ll[[x+1]], sumInd1[x]] y2[[x+1, 1]][scGaugeIdx2[x], sumInd1[x],sumInd2[x]] y3[[x+1, 1]][scGaugeIdx3[x],sumInd2[x],sumInd3[x]] y4[[x+1, 1]][scGaugeIdx4[x], sumInd3[x], Lr[[x+1]]],
				{sumInd1[x], 1, y2[[x+1, 3]]},
				{sumInd2[x], 1, y2[[x+1, 4]]},
	 			{sumInd3[x], 1, y4[[x+1, 3]]},
				{scGaugeIdx1[x], 1, y1[[x+1, 2]]},
				{scGaugeIdx2[x], 1, y2[[x+1, 2]]},
				{scGaugeIdx3[x], 1, y3[[x+1, 2]]},
				{scGaugeIdx4[x], 1, y4[[x+1, 2]]}
			]]]/@Range[NumberOfSubgroups])
		];
		
		
		SolveProd5[y1_, y2_, y3_, y4_, y5_, Ll_, Lr_, ScGauge_] := Join[
			{ 
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx12,scGenIdx2,scGenIdx22,scGenIdx3,scGenIdx32,scGenIdx4,scGenIdx42,scGenIdx5,scGenIdx52] GetGenProd[{y1, y2, y3, y4, y5}, {{scGenIdx1,scGenIdx12}, {scGenIdx2,scGenIdx22}, {scGenIdx3,scGenIdx32}, {scGenIdx4,scGenIdx42}, {scGenIdx5,scGenIdx52}}, Ll[[1]], Lr[[1]]] //.subProd,
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx3, 1, y3[[1,3]]},
					{scGenIdx4, 1, y4[[1,3]]},
					{scGenIdx5, 1, y5[[1,3]]},
					{scGenIdx12, 1, y1[[1,4]]},
					{scGenIdx22, 1, y2[[1,4]]},
					{scGenIdx32, 1, y3[[1,4]]},
					{scGenIdx42, 1, y4[[1,4]]},
					{scGenIdx52, 1, y5[[1,4]]}
				]]
			},
			(Function[{x},Refine[Sum[
				ScGauge[[x+1]][scGaugeIdx1[x], scGaugeIdx2[x], scGaugeIdx3[x], scGaugeIdx4[x], scGaugeIdx5[x]] y1[[x+1, 1]][scGaugeIdx1[x], Ll[[x+1]], sumInd1[x]] y2[[x+1, 1]][scGaugeIdx2[x], sumInd1[x],sumInd2[x]] y3[[x+1, 1]][scGaugeIdx3[x],sumInd2[x],sumInd3[x]] y4[[x+1, 1]][scGaugeIdx4[x], sumInd3[x], sumInd4[x]] y5[[x+1, 1]][scGaugeIdx5[x], sumInd4[x], Lr[[x+1]]],
				{sumInd1[x], 1, y2[[x+1, 3]]},
				{sumInd2[x], 1, y2[[x+1, 4]]},
	 			{sumInd3[x], 1, y4[[x+1, 3]]},
				{sumInd4[x], 1, y4[[x+1, 4]]},
				{scGaugeIdx1[x], 1, y1[[x+1, 2]]},
				{scGaugeIdx2[x], 1, y2[[x+1, 2]]},
				{scGaugeIdx3[x], 1, y3[[x+1, 2]]},
				{scGaugeIdx4[x], 1, y4[[x+1, 2]]},
				{scGaugeIdx5[x], 1, y5[[x+1, 2]]}
			]]]/@Range[NumberOfSubgroups])
		];
		
		(* traces and products of fermion type indices *)
		SolveProd[a_, b___, c_, i1_, i2_] := Sum[prod[
			a[i1, s1], SolveProd[b, s1, s2], c[s2, i2]],
			{s1, 1, FNumber[]}, {s2, 1, FNumber[]}
		];
		SolveProd[i1_, i2_] := KroneckerDelta[i1, i2];
		SolveProd[a_, i1_, i2_] := prod[a[i1,i2]];
		SolveTrace[a___] := Sum[tr[SolveProd[a, s, s]], {s, 1, FNumber[]}];
		
		(* combined traces over type and gauge indices for yukawa chains *)
		YukawaTrace[a___, SGauge_] := ReleaseHold[(ReleaseHold[SolveTrace[a] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]//.subYuk //.{tr[y1_, y2_]:>Hold[Times@@SolveTrace2[y1, y2, SGauge]], tr[y1_, y2_, y3_]:>Hold[Times@@SolveTrace3[y1, y2, y3, SGauge]], tr[y1_, y2_, y3_, y4_]:>Hold[Times@@SolveTrace4[y1, y2, y3, y4, SGauge]], tr[y1_, y2_, y3_, y4_, y5_]:>Hold[Times@@SolveTrace5[y1, y2, y3, y4, y5, SGauge]], tr[y1_, y2_, y3_, y4_, y5_, y6_]:>Hold[Times@@SolveTrace6[y1, y2, y3, y4, y5, y6, SGauge]]})];
		YukawaProd[a___, pl_, pr_, LstL_, LstR_, SGauge_] := ReleaseHold[(ReleaseHold[SolveProd[a, pl, pr] //. {adj[A_][i1_, i2_] :> adj[A[i2, i1]]} /.subYuk //.subProd]//.subYuk //.{tr[y1_, y2_]:>Hold[Times@@SolveTrace2[y1, y2, SGauge]], tr[y1_, y2_, y3_]:>Hold[Times@@SolveTrace3[y1, y2, y3, SGauge]], tr[y1_, y2_, y3_, y4_]:>Hold[Times@@SolveTrace4[y1, y2, y3, y4, SGauge]], tr[y1_, y2_, y3_, y4_, y5_]:>Hold[Times@@SolveTrace5[y1, y2, y3, y4, y5, SGauge]], tr[y1_, y2_, y3_, y4_, y5_, y6_]:>Hold[Times@@SolveTrace6[y1, y2, y3, y4, y5, y6, SGauge]], prod[y1_, y2_]:>Hold[Times@@SolveProd2[y1, y2, LstL, LstR, SGauge]], prod[y1_, y2_, y3_]:>Hold[Times@@SolveProd3[y1, y2, y3, LstL, LstR, SGauge]], prod[y1_, y2_, y3_, y4_]:>Hold[Times@@SolveProd4[y1, y2, y3, y4, LstL, LstR, SGauge]], prod[y1_, y2_, y3_, y4_, y5_]:>Hold[Times@@SolveProd5[y1, y2, y3, y4, y5, LstL, LstR, SGauge]]})];
		
		(* permutations *)
		Perm[f_[a_,b_,c_,d_]]:= f[a,b,c,d] + f[a,b,d,c] + f[a,c,b,d] + f[a,c,d,b] + f[a,d,b,c] + f[a,d,c,b] + f[b,a,c,d] + f[b,a,d,c] + f[b,c,a,d] + f[b,c,d,a] + f[b,d,a,c] + f[b,d,c,a] + f[c,a,b,d] + f[c,a,d,b] + f[c,b,a,d] + f[c,b,d,a] + f[c,d,a,b] + f[c,d,b,a] + f[d,a,b,c] + f[d,a,c,b] + f[d,b,a,c] + f[d,b,c,a] + f[d,c,a,b] + f[d,c,b,a];
		PermList[f_[a_,b_,c_,d_]]:={f[a,b,c,d], f[a,b,d,c], f[a,c,b,d], f[a,c,d,b], f[a,d,b,c], f[a,d,c,b], f[b,a,c,d], f[b,a,d,c], f[b,c,a,d], f[b,c,d,a], f[b,d,a,c], f[b,d,c,a], f[c,a,b,d], f[c,a,d,b], f[c,b,a,d], f[c,b,d,a], f[c,d,a,b], f[c,d,b,a], f[d,a,b,c], f[d,a,c,b], f[d,b,a,c], f[d,b,c,a], f[d,c,a,b], f[d,c,b,a]};
		PermList[s_ f_[a_,b_,c_,d_]]:={s f[a,b,c,d], s f[a,b,d,c], s f[a,c,b,d], s f[a,c,d,b], s f[a,d,b,c], s f[a,d,c,b], s f[b,a,c,d], s f[b,a,d,c], s f[b,c,a,d], s f[b,c,d,a], s f[b,d,a,c], s f[b,d,c,a], s f[c,a,b,d], s f[c,a,d,b], s f[c,b,a,d], s f[c,b,d,a], s f[c,d,a,b], s f[c,d,b,a], s f[d,a,b,c], s f[d,a,c,b], s f[d,b,a,c], s f[d,b,c,a], s f[d,c,a,b], s f[d,c,b,a]};
		
		(* scalar quartic products *)
		SolveSProd2[Q1_, Q2_, SContr_] := Times@@Join[
			{ (Q1[[1,1]] Q2[[1,1]])
				Sum[
					SContr[[1]][q1Idx1[0], q1Idx12[0], q1Idx2[0], q1Idx22[0], q1Idx3[0], q1Idx32[0], q1Idx4[0], q1Idx42[0], q2Idx1[0], q2Idx12[0], q2Idx2[0], q2Idx22[0], q2Idx3[0], q2Idx32[0], q2Idx4[0], q2Idx42[0]] Q1[[1,2]][q1Idx1[0], q1Idx12[0], q1Idx2[0], q1Idx22[0], q1Idx3[0], q1Idx32[0], q1Idx4[0], q1Idx42[0]] Q2[[1,2]][q2Idx1[0], q2Idx12[0], q2Idx2[0], q2Idx22[0], q2Idx3[0], q2Idx32[0], q2Idx4[0], q2Idx42[0]],
					{q1Idx1[0], 1, Q1[[1,3]]},
					{q1Idx2[0], 1, Q1[[1,4]]},
					{q1Idx3[0], 1, Q1[[1,5]]},
					{q1Idx4[0], 1, Q1[[1,6]]},
					{q2Idx1[0], 1, Q2[[1,3]]},
					{q2Idx2[0], 1, Q2[[1,4]]},
					{q2Idx3[0], 1, Q2[[1,5]]},
					{q2Idx4[0], 1, Q2[[1,6]]},
					{q1Idx12[0], 1, Q1[[1,7]]},
					{q1Idx22[0], 1, Q1[[1,8]]},
					{q1Idx32[0], 1, Q1[[1,9]]},
					{q1Idx42[0], 1, Q1[[1,10]]},
					{q2Idx12[0], 1, Q2[[1,7]]},
					{q2Idx22[0], 1, Q2[[1,8]]},
					{q2Idx32[0], 1, Q2[[1,9]]},
					{q2Idx42[0], 1, Q2[[1,10]]}
				]
			},
			(Function[{x},
				Sum[
					SContr[[1+x]][q1Idx1[x], q1Idx2[x], q1Idx3[x], q1Idx4[x], q2Idx1[x], q2Idx2[x], q2Idx3[x], q2Idx4[x]] Q1[[1+x,1]][q1Idx1[x], q1Idx2[x], q1Idx3[x], q1Idx4[x]] Q2[[1+x,1]][q2Idx1[x], q2Idx2[x], q2Idx3[x], q2Idx4[x]],
					{q1Idx1[x], 1, Q1[[1+x,2]]},
					{q1Idx2[x], 1, Q1[[1+x,3]]},
					{q1Idx3[x], 1, Q1[[1+x,4]]},
					{q1Idx4[x], 1, Q1[[1+x,5]]},
					{q2Idx1[x], 1, Q2[[1+x,2]]},
					{q2Idx2[x], 1, Q2[[1+x,3]]},
					{q2Idx3[x], 1, Q2[[1+x,4]]},
					{q2Idx4[x], 1, Q2[[1+x,5]]}
				]
			]/@Range[NumberOfSubgroups])
		];
		
		SolveSProd3[Q1_, Q2_, Q3_, SContr_] := Times@@Join[
			{ (Q1[[1,1]] Q2[[1,1]] Q3[[1,1]])
				Sum[
					SContr[[1]][q1Idx1[0], q1Idx12[0], q1Idx2[0], q1Idx22[0], q1Idx3[0], q1Idx32[0], q1Idx4[0], q1Idx42[0], q2Idx1[0], q2Idx12[0], q2Idx2[0], q2Idx22[0], q2Idx3[0], q2Idx32[0], q2Idx4[0], q2Idx42[0], q3Idx1[0], q3Idx12[0], q3Idx2[0], q3Idx22[0], q3Idx3[0],  q3Idx32[0], q3Idx4[0], q3Idx42[0]] Q1[[1,2]][q1Idx1[0], q1Idx12[0], q1Idx2[0], q1Idx22[0], q1Idx3[0], q1Idx32[0], q1Idx4[0], q1Idx42[0]] Q2[[1,2]][q2Idx1[0], q2Idx12[0], q2Idx2[0], q2Idx22[0], q2Idx3[0], q2Idx32[0], q2Idx4[0], q2Idx42[0]] Q3[[1,2]][q3Idx1[0], q3Idx12[0], q3Idx2[0], q3Idx22[0], q3Idx3[0],  q3Idx32[0], q3Idx4[0], q3Idx42[0]],
					{q1Idx1[0], 1, Q1[[1,3]]},
					{q1Idx2[0], 1, Q1[[1,4]]},
					{q1Idx3[0], 1, Q1[[1,5]]},
					{q1Idx4[0], 1, Q1[[1,6]]},
					{q2Idx1[0], 1, Q2[[1,3]]},
					{q2Idx2[0], 1, Q2[[1,4]]},
					{q2Idx3[0], 1, Q2[[1,5]]},
					{q2Idx4[0], 1, Q2[[1,6]]},
					{q3Idx1[0], 1, Q3[[1,3]]},
					{q3Idx2[0], 1, Q3[[1,4]]},
					{q3Idx3[0], 1, Q3[[1,5]]},
					{q3Idx4[0], 1, Q3[[1,6]]},
					{q1Idx12[0], 1, Q1[[1,7]]},
					{q1Idx22[0], 1, Q1[[1,8]]},
					{q1Idx32[0], 1, Q1[[1,9]]},
					{q1Idx42[0], 1, Q1[[1,10]]},
					{q2Idx12[0], 1, Q2[[1,7]]},
					{q2Idx22[0], 1, Q2[[1,8]]},
					{q2Idx32[0], 1, Q2[[1,9]]},
					{q2Idx42[0], 1, Q2[[1,10]]},
					{q3Idx12[0], 1, Q3[[1,7]]},
					{q3Idx22[0], 1, Q3[[1,8]]},
					{q3Idx32[0], 1, Q3[[1,9]]},
					{q3Idx42[0], 1, Q3[[1,10]]}
				]
			},
			(Function[{x},
				Sum[
					SContr[[1+x]][q1Idx1[x], q1Idx2[x], q1Idx3[x], q1Idx4[x], q2Idx1[x], q2Idx2[x], q2Idx3[x], q2Idx4[x], q3Idx1[x], q3Idx2[x], q3Idx3[x], q3Idx4[x]] Q1[[1+x,1]][q1Idx1[x], q1Idx2[x], q1Idx3[x], q1Idx4[x]] Q2[[1+x,1]][q2Idx1[x], q2Idx2[x], q2Idx3[x], q2Idx4[x]] Q3[[1+x,1]][q3Idx1[x], q3Idx2[x], q3Idx3[x], q3Idx4[x]],
					{q1Idx1[x], 1, Q1[[1+x,2]]},
					{q1Idx2[x], 1, Q1[[1+x,3]]},
					{q1Idx3[x], 1, Q1[[1+x,4]]},
					{q1Idx4[x], 1, Q1[[1+x,5]]},
					{q2Idx1[x], 1, Q2[[1+x,2]]},
					{q2Idx2[x], 1, Q2[[1+x,3]]},
					{q2Idx3[x], 1, Q2[[1+x,4]]},
					{q2Idx4[x], 1, Q2[[1+x,5]]},
					{q3Idx1[x], 1, Q3[[1+x,2]]},
					{q3Idx2[x], 1, Q3[[1+x,3]]},
					{q3Idx3[x], 1, Q3[[1+x,4]]},
					{q3Idx4[x], 1, Q3[[1+x,5]]}
				]
			]/@Range[NumberOfSubgroups])
		];
		
		
		(* number of real scalars and weyl fermions *)
		SNumber[] := If[RealScalarList == {}, 0, Dimensions[RealScalarList][[1]]];
		FNumber[] := If[WeylFermionList == {}, 0, Dimensions[WeylFermionList][[1]]];
		
		(* workaround a mathematica bug *)
		ListPosition[A_, B___] := Position[A//. {{} -> $EMPTYLIST}, B];
		
		(* Error Messages *)
		Gauge::RepMismatch = "Representation list does not match number of subgroups";
		WeylFermion::RepMismatch = "Representation list does not match number of subgroups";
		RealScalar::RepMismatch = "Representation list does not match number of subgroups";
		Yukawa::ContractionError = "Number of gauge contractions does not match number of subgroups";
		Yukawa::UnknownParticle = "Undefined particle in Yukawa sector";
		Quartic::ContractionError = "Number of gauge contractions does not match number of subgroups";
		Quartic::UnknownParticle = "Undefined particle in scalar sector";
		
		Reset[];
	(*End[];*)
EndPackage[];
