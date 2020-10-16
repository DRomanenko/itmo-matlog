ALEX = tokenizer
HAPPY = parser
HSFILE = main

all: compile run remove

compile:
	alex ${ALEX}.x
	happy ${HAPPY}.y
	ghc -O3 ${HSFILE}.hs ${ALEX}.hs ${HAPPY}.hs

run:
	./main

remove:
	rm -f ${HSFILE} ${ALEX}.hs ${HAPPY}.hs *.hi *.o