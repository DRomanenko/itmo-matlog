ALEX = tokenizer
HAPPY = parser
HSFILE = main.hs

all: compile run remove

compile:
	alex ${ALEX}.x
	happy ${HAPPY}.y
	ghc -O2 ${HSFILE} ${ALEX}.hs ${HAPPY}.hs

run:
	./main

remove:
	rm -f ${ALEX}.hs ${HAPPY}.hs *.hi *.o
