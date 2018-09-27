CC=coqc

aula: aula11.o 

aula11.o: aula9.o
	$(CC) aula11_prop_indutivas.v

aula9.o: aula8.o
	$(CC) aula09_logica.v

aula8.o: aula7.o
	$(CC) aula08_taticas.v

aula7.o: aula6.o
	$(CC) aula07_alta_ordem.v

aula6.o: aula5.o
	$(CC) aula06_poli.v

aula5.o: aula4.o
	$(CC) aula05_listas.v

aula4.o: aula3.o
	$(CC) aula04_inducao.v

aula3.o: aula2.o
	$(CC) aula03_provas.v

aula2.o: 
	$(CC) aula02_gallina.v
clean:
	rm *.vo *.glob *.aux
