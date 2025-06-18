SOURCES = ir.o
LIBRARIES = glib-2.0

LDFLAGS = $(shell pkg-config --libs ${LIBRARIES})
CRT1 = $(shell gcc -print-file-name=crt1.o)
CRTI = $(shell gcc -print-file-name=crti.o)
CRTN = $(shell gcc -print-file-name=crtn.o)
LDPATH = $(shell gcc -print-file-name=ld-linux-x86-64.so.2)

build:
	cargo run ${CARGOFLAGS}
	ld -o ir -dynamic-linker ${LDPATH} ${CRT1} ${CRTI} ${CRTN} -lc ir.o ${LDFLAGS}

clean:
	rm ir ir.o
