SOURCES = ir.o
LIBRARIES = glib-2.0

LDFLAGS = $(shell pkg-config --libs ${LIBRARIES})

build:
	cargo run
	ld -o ir -dynamic-linker /lib64/ld-linux-x86-64.so.2 /usr/lib/crt1.o /usr/lib/crti.o -lc ir.o /usr/lib/crtn.o ${LDFLAGS}

clean:
	rm ir ir.o
