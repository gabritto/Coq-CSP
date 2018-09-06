CC=coqc
CFLAGS= 

aula: aula6.o 

aula6.o: aula5.o
	coqc aula06_poli.v

aula5.o: aula4.o
	coqc aula05_listas.v

aula4.o: aula3.o
	coqc aula04_inducao.v

aula3.o: aula2.o
	coqc aula03_provas.v

aula2.o: 
	coqc aula02_gallina.v
clean:
	rm *.vo *.glob
