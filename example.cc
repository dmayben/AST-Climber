#include <cstdio>
#include <cstdlib>
#include <cstring>

char * globalVar;

void zero_out_memory(char* G)
{
    int i;
    for(i = 0; i < 100; i++)
    {
        G[i] = '\0';
    }
}

void copy_process(char* Y) {
    char* Y_deepcp = (char*)malloc(100*sizeof(char));
    memcpy(Y_deepcp, Y, 100*sizeof(char));
    char* other = (char*)malloc(99*sizeof(char));
    strcpy(other, "Non-sensitive data");
    free(Y_deepcp);
    free(other);
}

void CWE244_dummy()
{
    char* X = (char*)malloc(100*sizeof(char));
    char* X_shallowcp = X;
    char* X_shallowcp2;
    char* X_shallowcp3 = X_shallowcp2 = X;
    if(fgets(X, 100, stdin) == NULL) {
        printf("fgets() failed");
        X[0] = '\0';
    }
    
    copy_process(X_shallowcp);
    zero_out_memory(X);
    free(X);
}

int add(int a, int b, int c)
{
    return a+b+c;
}


int main(int argc, char** argv){
    globalVar = (char*)malloc(100*sizeof(char));
    CWE244_dummy();
    free(globalVar);
    int d = 0;
    int e = 0;
    int f = 0;
    if(add(d,2,f))
    {
        d = e;
    }
    else
    {
        d = f;
    }

    while(add(d,e,f))
    {
        d = 0;
    }

    do {
        e = 0;
    } while (add(d,e,f));

    for(d = 0; d < add(d,e,f); d++)
    {
        f = 0;
    }

    switch(add(d,e,f))
    {
        case 0: break;
        case 1: break;
        default: break;
    }

    return 0;
}