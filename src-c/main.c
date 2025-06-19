extern int printf(const char *fmt, ...);

int foobar(int i) {
    if (i > 101) {
        return 0;
    }

    if (i % 5 == 0) {
        if (i % 7 == 0) {
            printf("foobar\n");
        } else {
            printf("foo\n");
        }
    } else if (i % 7 == 0) {
        printf("bar\n");
    } else {
        printf("%d\n", i);
    }

    return foobar(i + 1);
}

int main() {
    foobar(1);

    return 0;
}
