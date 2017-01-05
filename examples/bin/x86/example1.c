
int function_of_interest(int arg) {
    return arg % 2;
}

int some_function(char *input) {
    int len = 0;
    for(; *input++; len++) {}
    return function_of_interest(len);
}

int main(int argc, char *argv[]) {
    return some_function(argv[1]);
}
