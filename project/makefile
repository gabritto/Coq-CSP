CC=coqc

project: traces

traces: csp_syntax
	$(CC) traces.v 

csp_syntax: 
	$(CC) csp_syntax.v    
    
clean:
	rm *.vo *.glob *.aux *.crashcoqide
