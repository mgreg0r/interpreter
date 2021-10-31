all:
	ghc --make interpreter.hs -o interpreter

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

