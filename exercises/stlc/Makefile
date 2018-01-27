TARGET = main.byte

default: $(TARGET)

hard: $(TARGET)
	./$<

%.byte: $(wildcard *.ml)
	corebuild $@
