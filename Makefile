%.vo : %.v
	coqc $*.v

Extraction.vo : Union_STV.vo

Lib.hs : Extraction.vo

Main : Main.hs Lib.hs
	ghc -o Main Main.hs

small : Candidates_Small.hs Main.hs Lib.hs
	cp Candidates_Small.hs Candidates.hs; ghc -o small Main.hs
	

actbri : ACTBri.hs Main.hs Lib.hs
	cp ACTBri.hs Candidates.hs; ghc -o actbri Main.hs

actgin : ACTGin.hs Main.hs Lib.hs
	cp ACTGin.hs Candidates.hs; ghc -o actgin Main.hs

actmol : ACTMol.hs Main.hs Lib.hs
	cp ACTMol.hs Candidates.hs; ghc -o actmol Main.hs

actb : ACTB.hs Main.hs Lib.hs
	cp ACTB.hs Candidates.hs; ghc -o actb Main.hs

actg : ACTG.hs Main.hs Lib.hs
	cp ACTG.hs Candidates.hs; ghc -o actg Main.hs

actm : ACTM.hs Main.hs Lib.hs
	cp ACTM.hs Candidates.hs; ghc -o actm Main.hs

random : Candidates_Random.hs Main.hs Lib.hs
	cp Candidates_Random.hs Candidates.hs; ghc Candidates.hs; ghc -o random Main.hs
	
random100 : random
	./rand.pl 100 > random_election.txt; ./random

random1000 : random
	./rand.pl 1000 > random_election.txt; ./random

random10000 : random
	./rand.pl 10000 > random_election.txt; ./random

random100 : random
	./rand.pl 100 > random_election.txt; ./random

clean: 
	-rm *.vo *.glob *.hi Main Lib.* *.o 2>/dev/null
