# Konjektoj kaj nepruvitaj esplorasertoj

[English](../../en/reference/CONJECTURES.md) · [简体中文](../../zh-CN/reference/CONJECTURES.md) ·
[日本語](../../ja/reference/CONJECTURES.md) · [Esperanto](CONJECTURES.md)

La registro enhavas Lean-propoziciojn kies asertoj kompiliĝas sed kies pruvoj
ankoraŭ ne estas kerne kontrolitaj. Aktiva ero devas havi la markon
`FORMALIZED_BUT_UNPROVED` kaj nomi sian deklaron. La maŝina kanona registro estas
[`CONJECTURES.md`](../../../CONJECTURES.md).

## Nuna registro

Nun ne ekzistas aktiva `FORMALIZED_BUT_UNPROVED`-propozicio. Tio ne signifas,
ke la esplorprogramo estas kompleta. Konstruaj taskoj, kiuj ankoraŭ ne estas
precizaj Lean-propozicioj, ne estas kaŝe traktataj kiel supozoj aŭ aksiomoj.

## Ĝenerala celo kaj malfermaj teoremfamilioj

Ript celas unuigi klasikan probablon, kvantumajn procezojn, kaŭzajn modelojn,
komputadon, semantikan informon kaj termodinamikon kiel malsamajn modelojn de
rimed-limigitaj informprocezoj. La totala modelbikategorio, heterogenaj
rimedmapoj, kostpuŝo de komuna sintakso, inversebla esprimtraduko, reprezento de
interpretoj kaj ekzakta libera buĝeto jam estas kompilitaj.

La unua efektiva komuna-sintaksa tranĉo ankaŭ kompiliĝas: unu Bulea turna
generatoro estas realigita per la ekzakta probabla, Pauli-X-a kvantuma, finia
kaŭza, plurdimensia komputa, task-semantika kaj Gibbs-konserva termika modeloj.
`sixModelFlipAgreement` pakas la ses observeblajn ekvaciojn.

Restas malfermaj:

1. etendo de la Bulea tranĉo al komuna kompona sintakso, kiu montras la
   karakterizajn strukturojn de ĉiuj ses modelfamilioj;
2. reprezentaj kaj konservemaj teoremoj pri la ekzakta bildo de ĉiu interpreto;
3. relativa aŭ, kie pravigite, absoluta kompleteco;
4. univalenta aŭ complete-Segal-semantiko de la totala heterogena modelteorio
   kun universala eco.

## Limo de la klasifika diagramo

Estas pruvitaj la natura izomorfio kun `n ↦ Map(Δ[n], N(M.Object))`, veraj
limaj kongruaj limoj, la universala lift, fibrado de ĉiuj kongruaj mapoj,
Kan/strikta-Segal-strukturo de horizontalaj vicoj, la
`SSet.NerveEquivalenceWitness` de la reala kompleteca mapo kaj la pakaĵo
`SSet.GroupoidalCompleteSegal`.

La fiksita Mathlib ne havas klason de malfortaj ekvivalentoj por simpliciaj
aroj aŭ kompletan Quillen-modelan strukturon; tial denaska norma
complete-Segal-ekzemplero ankoraŭ ne estas esprimebla.

## Limo de bikategoria lokalizado

`IsBicategoricalLocalization` postulas, ke markitaj 1-morfismoj fariĝu
adjunktaj ekvivalentoj, ke ĉiu inversiga pseŭdofunktoro havu duesencan
faktorigon, kaj ke antaŭkompono estu ekvivalento en la lokaj kategorioj de
fortaj transformoj kaj modifoj. La Ript-specialigo estas
`IsCostExactBicategoricalLocalization`.

Kompilitaj partoj inkluzivas:

- la kompleta identeca bazkazo kaj konkreta netriviala nul-kosta kontraŭekzemplo;
- libergrupa lokalizado de la `Fin 2`-iranta sago kun eksplicita inverso;
- parametrigita produkto, kiu lokalizas nur la irantan koordinaton kaj retenas
  neinversigeblan Bulean forĵetan 2-ĉelon;
- faktorigoj por retenitaj, grupoidvaloraj, disigeblaj miksitaj familioj kaj
  ilia adjunkt-ekvivalenta fermo;
- finpunkta normformo, maldikeco kaj ekvivalento kun la kodiskreta grupoido sur
  `Fin 2`;
- levoj de fortaj transformoj kaj modifoj, kun lokaj antaŭkomponaj ekvivalentoj;
- `PrelaxFunctor`-agado por arbitra eble nedisigebla inversiga pseŭdofunktoro,
  identeca komparo kaj ĉiuj ok finpunkt-normaligitaj duopaj komponiloj;
- maldekstra/dekstra natureco, ambaŭ unuigaj leĝoj, plena antaŭa asocieco kaj la
  unua vera inversa branĉo `1→0→0→0`.

Restas dek inversaj aŭ nuligaj asociecaj finpunktsekvoj, pseŭdofunktora pakaĵo,
la fina adjunkta ekvivalento de fontfaktorigo kaj ĝeneraligo al la plena
rimed-proceza bikategorio. Tio estas la mankanta tutmonda `lift`-kampo.

## Jam finitaj ordinaraj lokalizadoj

La identeca, skeleta kaj limigita Yoneda-funktoroj de la interna grupoido
plenumas Mathlib `Functor.IsLocalization`. La homotopia 1-kategorio de la
modelbikategorio ankaŭ havas Gabriel–Zisman-lokalizadon ĉe kost-reflektaj klasoj.
Neinversigebla markita sago montras veran aldonon de inverso; aparta
neinversigebla 2-ĉelo montras kial loke diskreta celo ne povas reteni plenan
dudimensian informon.

## Lastatempe finita: finia stokasta Blackwell-inverso

`Ript.Models.Decision.RationalSeparation.finiteBlackwellShermanStein` estas
kerne kontrolita. Por ne-malplena finia kaŝstata tipo, la riska ordo por ĉiuj
ekzaktaj finiaj decidproblemoj implicas ekzaktan stokastan garbling-on. La
`EmptyParameterBoundary`-kontraŭekzemplo pruvas, ke ne-malpleneco estas necesa.

La pruvo ligas racionalan simpleksan reprezenton de garbling, reflektadon de
racionala punkto el reela al racionala konveksa envolvaĵo, Hahn–Banach-an
striktan apartigon kun racionala denseco, kaj konverton de signita apartigilo al
nenegativ-racionala decida atestilo. La supozoj estas
`[propext, Classical.choice, Quot.sound]`; neniu LP-solvilo estas eltirita.

## Algoritma limo

Por finia reela energispektro, ekzaktaj racionalaj Gibbs-probabloj ekzistas
precize kiam ĉiuj Boltzmann-proporcioj al referenca stato estas pozitivaj
racionaloj. Ruleblaj racional-pezaj ekzemploj kaj pruvita `sqrt 2`-obstrukco
ekzistas, sed ne ekzistas ĝenerala algoritmo por decidi egalecon de arbitraj
reelaj eksponentaj esprimoj.
