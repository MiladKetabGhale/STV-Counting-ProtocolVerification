Source files for the paper 
  "A Formally Verified Single Transferable Vote Scheme with Fraction Values"

Dependencies :

- The formal proofs were developed with the Coq proof assistant. We
  have used Coq version 8.4pl3 (January 2014)

- The extracted Haskell code was compliled under ghc version 8.0.2

- The randomly generated ballots used in the benchmarks were generated using Haskell 8.0.2 .

The code was developed and tested under Linux.


Files :

- Union_STV.v which contains the formalisation reported in the paper, plus the generic STV which was not mentioned in the paper.

- Extraction.v defines the extraction of the development into Haskell where all Coq data structures are extracted as is.

- small_election.txt: the ballots used in the Figure 5 of the paper to show an instance of a certificate.

- ACTBri.txt : is the list of ballots of the Legislative Assembly election 2008 in Brindabella electorate.

-ACTGin.txt : is the list of ballots of the Legislative Assembly election 2008 in Ginninderra electorate.

-ACTMol.txt : is the list of ballots of the Legislative Assembly election 2008 in Molonglo electorate.

-ACTB1.txt : is the list of ballots of the Legislative Assembly election 2012 in Brindabella electorate.

-ACTG1.txt : is the list of ballots of the Legislative Assembly election 2012 in Ginninderra electorate.

-ACTM1.txt : is the list of ballots of the Legislative Assembly election 2012 in Molonglo electorate.



Building the executables.

- To reproduce the example in the paper, do "make small". This
  creates an executable "small". Running this reads from the file
  "small_election.txt" and reproduces the count together with the
  certificate. Run by executing "./small" in a shell in the
  top-level directory created by extracting the tar file that
  contains this file, "ANU-Union".

- To run the extracted code on the ballots of the ACT legislative
  assembly in the Molonglo electorate 2008, do "make actmol". This
  creates an executable "actmol". Running this reads from the file
  "ACTelection.txt" and reproduces the count together with the
  certificate. Run by executing "./actmol" in a shell in the
  top-level directory created by extracting the tar file that
  contains this file, "ANU-Union". The real names of the candidates
  have been abbreviated to three-letter acronyms. In order to run the program on other ACT electorate, replace actmol in "make actmol" by the related command name and proceed similarly as above.

- To run elections with randomly generated ballots, do "make
  random". This reads from a file called "random_election.txt". Use
  the file "rand.pl" to generate random ballots, as e.g. 
    ./rand.pl 100 > random_election.txt; ./random
  Alternatively, we have provided a small number of instances in the
  Makefile. For elections with 100, 1000, 10000 candidates, you can
  simply do "make random100, make random1000, make random10000".



