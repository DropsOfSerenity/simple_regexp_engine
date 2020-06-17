#include <string.h>
#include <stdlib.h>
#include <stdio.h>

void
unsafe_concat_char(char *str, char c)
{
    unsigned len = strlen(str);

    str[len] = c;
    str[len + 1] = 0;
}

char *
add_explicit_concatenation_op(const char *regexp)
{
    unsigned size = strlen(regexp);
    char *result = calloc(1, size * 2 + 1);
    
    for (unsigned i = 0; i < size; ++i)
    {
        char at = regexp[i];
        unsafe_concat_char(result, at);

        if (at == '(' || at == '|')
        {
            continue;
        }

        if (i < size - 1) {
            char next = regexp[i + 1];

            if (next == '|' || next == '+' || next == '*' || next == ')' || next == '?')
            {
                continue;
            }

            unsafe_concat_char(result, '.');
        }
    }

    return result;
}

int
operator_precedence(char c)
{
    switch(c)
    {
        case '.': return 0;
        case '|': return 1;
        case '+':
        case '?':
        case '*': return 2;
    }
}


int
is_operator(char c)
{
    return c == '|' || c == '+' || c == '.' || c == '*' || c == '?';
}

char *
regexp_to_postfix_shunting_yard(const char *regexp)
{
    unsigned size = strlen(regexp) * 2;
    char *result = calloc(1, size + 1);

    char *stack = calloc(1, size * sizeof(*stack));
    char *start = stack;
    char *stackp = (start + size);
    char *last = (start + size);

#define pop() *stackp++
#define push(c) *--stackp = c

    for (unsigned i = 0; i < strlen(regexp); ++i)
    {
        char token = regexp[i];

        if (is_operator(token))
        {
            int precedence = operator_precedence(token);
            
            while ((stackp != last)
                   && (*stackp != '(')
                   && (operator_precedence(*last) >= precedence))
            {
                char c = pop();
                unsafe_concat_char(result, c);
            }
            push(token);
        }
        else if (token == '(') {
            push(token);
        }
        else if (token == ')') {
            while (*stackp != '(')
            {
                unsafe_concat_char(result, pop());
            }
            if (*stackp == '(')
            {
                pop(); // discard
            }
            else
            {
                /* TODO(justin): Unmatched Paren */
            }
        }
        else
        {
            unsafe_concat_char(result, token);
        }
    }

    while (stackp != last)
    {
        unsafe_concat_char(result, pop());
    }

    free(stack);
#undef pop
#undef push

    return result;
}

typedef struct NFA_State {
    int is_end;

    struct NFA_State *char_transitions[128];
    struct NFA_State **epsilon_transitions;
    unsigned epsilon_count;
} NFA_State;

void
add_epsilon(NFA_State *state, NFA_State *to)
{
    ++state->epsilon_count;
    state->epsilon_transitions = realloc(
        state->epsilon_transitions,
        sizeof(NFA_State *) * state->epsilon_count);
    state->epsilon_transitions[state->epsilon_count - 1] = to;
}

void
add_char_transition(NFA_State *state, NFA_State *to, char c)
{
    state->char_transitions[(int)c] = to;
}

typedef struct {
    NFA_State *start;
    NFA_State *out;
} NFA_Fragment;

NFA_Fragment
init_frag()
{
    NFA_Fragment result;
    result.start = malloc(sizeof(*result.start));
    result.out = malloc(sizeof(*result.out));
    result.start->is_end = 0;
    result.out->is_end = 1;
    return result;
}

NFA_Fragment
postfix_to_nfa(char *postfix_regexp)
{
    unsigned size = strlen(postfix_regexp);
    NFA_Fragment *fstack = malloc(sizeof(*fstack) * size);
    NFA_Fragment *stackp = fstack + size;
    NFA_Fragment *last = fstack + size;

#define pop() *stackp++
#define push(frag) *--stackp = frag

    for (unsigned i = 0; i < size; ++i)
    {
        char at = postfix_regexp[i];

        switch(at)
        {
            case '.': {
                NFA_Fragment right = pop();
                NFA_Fragment left = pop();

                left.out->is_end = 0;
                add_epsilon(left.out, right.start);

                NFA_Fragment frag;
                frag.start = left.start;
                frag.out = right.out;
                push(frag);
            } break;

            case '|': {
                /* NOTE(justin): Union Expression */
                NFA_Fragment right = pop();
                NFA_Fragment left = pop();

                NFA_Fragment frag = push(init_frag());
                add_epsilon(frag.start, right.start);
                add_epsilon(frag.start, left.start);

                left.out->is_end = 0;
                add_epsilon(left.out, frag.out);

                right.out->is_end = 0;
                add_epsilon(right.out, frag.out);
            } break;

            case '?': {
                NFA_Fragment op = pop();

                NFA_Fragment frag = push(init_frag());
                add_epsilon(frag.start, frag.out);
                add_epsilon(frag.start, op.start);
                add_epsilon(op.out, frag.out);
                op.out->is_end = 0;
            } break;

            case '+': {
                NFA_Fragment op = pop();

                NFA_Fragment frag = push(init_frag());
                add_epsilon(frag.start, op.start);

                add_epsilon(op.out, op.start);
                add_epsilon(op.out, frag.out);
                op.out->is_end = 0;
            } break;

            case '*': {
                NFA_Fragment op = pop();

                NFA_Fragment frag = push(init_frag());
                add_epsilon(frag.start, op.start);
                add_epsilon(frag.start, frag.out);

                add_epsilon(op.out, op.start);
                add_epsilon(op.out, frag.out);
                op.out->is_end = 0;
            } break;

            default: {
                NFA_Fragment frag = push(init_frag());
                add_char_transition(frag.start, frag.out, at);
            } break;
        }
    }

    NFA_Fragment result = pop();
    free(fstack);

#undef pop
#undef push

    return result;
}

typedef struct {
    NFA_State **visited;
    unsigned count;
    unsigned capacity;
} DFS_Visited_Nodes;

DFS_Visited_Nodes
init_visited(unsigned capacity)
{
    DFS_Visited_Nodes result;
    result.visited = malloc(sizeof(*result.visited) * capacity);
    result.count = 0;
    result.capacity = capacity;
    return result;
}

int
already_visited(DFS_Visited_Nodes visited, NFA_State *node)
{
    int result = 0;
    for (unsigned i = 0; i < visited.count; ++i)
    {
        if (visited.visited[i] == node)
        {
            result = 1;
            break;
        }
    }
    return result;
}

int
dfs_recursive_search(NFA_State *root, const char *word, unsigned matched_num, DFS_Visited_Nodes visited)
{
    unsigned size = strlen(word);

    if (already_visited(visited, root))
    {
        return 0;
    }

    visited.visited[visited.count++] = root;

    if (matched_num == size)
    {
        if (root->is_end)
        {
            return 1;
        }

        /* NOTE(justin): Traverse Epsilon Paths */
        for (unsigned i = 0; i < root->epsilon_count; ++i)
        {
            if (dfs_recursive_search(root->epsilon_transitions[i], word, matched_num, visited))
            {
                return 1;
            }
        }
    }
    else
    {
        NFA_State *transition = root->char_transitions[word[matched_num]];
        if (transition)
        {
            if (dfs_recursive_search(
                    transition,
                    word,
                    matched_num + 1,
                    init_visited(visited.capacity)))
            {
                return 1;
            }
        }
        else
        {
            for (unsigned i = 0; i < root->epsilon_count; ++i)
            {
                if (dfs_recursive_search(root->epsilon_transitions[i], word, matched_num, visited))
                {
                    return 1;
                }
            }            
        }

    }
    return 0;
}

NFA_Fragment
r(char *regexp)
{
    char *concatted = add_explicit_concatenation_op(regexp);
    char *postfix = regexp_to_postfix_shunting_yard(concatted);
    NFA_Fragment result = postfix_to_nfa(postfix);

    free(concatted);
    free(postfix);

    return result;
}

int
match(NFA_Fragment nfa, char *search)
{
    /* TODO(justin): Create base compiled_regexp object, which has
     * number of nodes. */
    return dfs_recursive_search(nfa.start, search, 0, init_visited(256));
}

void
regex_match(char *regexp, char *search)
{
    NFA_Fragment compiled = r(regexp);
    const char *format = "%-10s %-13s \"%s\"\n";

    if (match(compiled, search))
    {
        printf(format, regexp, "\033[01;32mmatched\033[00m", search);
    }
    else
    {
        printf(format, regexp, "\033[01;31mdid not match\033[00m", search);
    }
}

int
main()
{
    regex_match("(zz)+", "zz");
    regex_match("(x|y)*z", "xyxyyyxxxz");
    regex_match("(x|y)*z+", "xy");
    regex_match("(x|y)*z+", "xyzzz");
    regex_match("(1|2|3|4|5|6|7|8|9)+", "1423");
    regex_match("(1|2|3|4|5|6|7|8|9)+", "123abc");
    regex_match("a?", "");
    regex_match("a?", "a");
    regex_match("a?", "aa");
    regex_match("hell(a|o)?", "hello");
   
    return 0;
}
