use core::arch::x86_64::{CpuidResult, __cpuid_count};

#[derive(Clone, Copy, Debug)]
pub enum Manufacturer {
    AmdK5Sample,           // "AMDisbetter!" – early engineering samples of AMD K5 processor
    Amd,                   // "AuthenticAMD" – AMD
    IdtWinChipCentaur, // "CentaurHauls" – IDT WinChip/Centaur (Including some VIA and Zhaoxin CPUs)
    Cyrix,             // "CyrixInstead" – Cyrix/early STMicroelectronics and IBM
    Intel,             // "GenuineIntel" – Intel
    Transmeta,         // "TransmetaCPU" – Transmeta, "GenuineTMx86" – Transmeta
    NationalSemiconductor, // "Geode by NSC" – National Semiconductor
    NexGen,            // "NexGenDriven" – NexGen
    Rise,              // "RiseRiseRise" – Rise
    SiS,               // "SiS SiS SiS " – SiS
    Umc,               // "UMC UMC UMC " – UMC
    Via,               // "VIA VIA VIA " – VIA
    DmPVortex86,       // "Vortex86 SoC" – DM&P Vortex86
    Zhaoxin,           // "  Shanghai  " – Zhaoxin
    Hygon,             // "HygonGenuine" – Hygon
    RdcSemiconductors, // "Genuine  RDC" – RDC Semiconductor Co. Ltd.[5]
    McstElbrus,        // "E2K MACHINE" – MCST Elbrus

    Ao486, // "MiSTer AO486" – ao486 CPU[6]
    // "GenuineIntel" – v586 core[7] (this is identical to the Intel ID string)
    Bhyve,           // "bhyve bhyve " – bhyve
    Kvm,             // "KVMKVMKVM\0\0\0" – KVM, \0 denotes an ASCII NUL character
    Qemu,            // "TCGTCGTCGTCG" – QEMU
    MicrosoftHyperV, // "Microsoft Hv" – Microsoft Hyper-V or Windows Virtual PC
    MicrosoftXta,    // "MicrosoftXTA" – Microsoft x86-to-ARM[8]
    Parallels, // " lrpepyh  vr" – Parallels (it possibly should be "prl hyperv ", but it is encoded as " lrpepyh vr" due to an endianness mismatch)[citation needed]
    Vmware,    // "VMwareVMware" – VMware
    Xen,       // "XenVMMXenVMM" – Xen HVM
    ProjectAcrn, // "ACRNACRNACRN" – Project ACRN
    QnxHypervisor, // " QNXQVMBSQG " – QNX Hypervisor
    // "GenuineIntel" – Apple Rosetta 2[9]
    AppleRosetta2, // "VirtualApple" – Newer versions of Apple Rosetta 2
    Unknown,
}

impl<'a> From<&'a str> for Manufacturer {
    fn from(s: &'a str) -> Self {
        match s {
            "AMDisbetter!" => Self::AmdK5Sample,
            "AuthenticAMD" => Self::Amd,
            "CentaurHauls" => Self::IdtWinChipCentaur,
            "CyrixInstead" => Self::Cyrix,
            "GenuineIntel" => Self::Intel,
            "TransmetaCPU" | "GenuineTMx86" => Self::Transmeta,
            "Geode by NSC" => Self::NationalSemiconductor,
            "NexGenDriven" => Self::NexGen,
            "RiseRiseRise" => Self::Rise,
            "SiS SiS SiS " => Self::SiS,
            "UMC UMC UMC " => Self::Umc,
            "VIA VIA VIA " => Self::Via,
            "Vortex86 SoC" => Self::DmPVortex86,
            "  Shanghai  " => Self::Zhaoxin,
            "HygonGenuine" => Self::Hygon,
            "Genuine  RDC" => Self::RdcSemiconductors,
            "E2K MACHINE\0" => Self::McstElbrus,
            "MiSTer AO486" => Self::Ao486,
            "bhyve bhyve " => Self::Bhyve,
            "KVMKVMKVM\0\0\0" => Self::Kvm,
            "TCGTCGTCGTCG" => Self::Qemu,
            "Microsoft Hv" => Self::MicrosoftHyperV,
            "MicrosoftXTA" => Self::MicrosoftXta,
            " lrpepyh  vr" => Self::Parallels,
            "VMwareVMware" => Self::Vmware,
            "XenVMMXenVMM" => Self::Xen,
            "ACRNACRNACRN" => Self::ProjectAcrn,
            " QNXQVMBSQG " => Self::QnxHypervisor,
            "VirtualApple" => Self::AppleRosetta2,
            _ => Self::Unknown,
        }
    }
}

const EAX_LEAF_MANUFACTURER_INFO: u32 = 0;
const EAX_LEAF_PROCESSOR_INFO: u32 = 1;

const EAX_LEAF_GET_HIGHEST_EXTENDED_FUNCTION: u32 = 0x8000_0000;

#[derive(Clone, Copy, Debug)]
pub struct Cpuid {
    #[allow(dead_code)]
    max_leaves: u32,
    #[allow(dead_code)]
    max_extended_leaves: u32,
    manufacturer: Manufacturer,
}

impl Cpuid {
    pub fn init() -> Self {
        let CpuidResult { eax, ebx, ecx, edx } =
            unsafe { __cpuid_count(EAX_LEAF_MANUFACTURER_INFO, 0) };
        let max_leaves = eax;

        #[repr(C, packed)]
        struct ManufacturerStr {
            ebx: u32,
            edx: u32,
            ecx: u32,
        }
        const _: () = assert!(core::mem::size_of::<ManufacturerStr>() == 12);
        let manu_str = ManufacturerStr { ebx, edx, ecx };
        let brand_string_start = &manu_str as *const ManufacturerStr as *const u8;
        let slice = unsafe {
            // Safety: ManufacturerStr is laid out with repr(C, packed) and exactly 12 byte long
            core::slice::from_raw_parts(brand_string_start, core::mem::size_of::<ManufacturerStr>())
        };
        let manu_str = core::str::from_utf8(slice).unwrap_or("InvalidVendorString");
        let manufacturer = Manufacturer::from(manu_str);

        let CpuidResult {
            eax: max_extended_leaves,
            ..
        } = unsafe { __cpuid_count(EAX_LEAF_GET_HIGHEST_EXTENDED_FUNCTION, 0) };

        Self {
            max_leaves,
            max_extended_leaves,
            manufacturer,
        }
    }

    pub fn manufacturer(&self) -> Manufacturer {
        self.manufacturer
    }

    pub fn processor_info(&self) -> ProcessorInfo {
        let CpuidResult { eax, ebx, ecx, edx } =
            unsafe { __cpuid_count(EAX_LEAF_PROCESSOR_INFO, 0) };
        ProcessorInfo::new(eax, ebx, ecx, edx)
    }
}

// CPUID EAX=1: Processor Version Information in EAX EAX
// +-----------------------------------------------------------------------------------------------------------------+
// | 31    28 | 27              20 | 19             16 | 15    14 | 13          12 | 11      8 | 7   4 | 3         0 |
// +-----------------------------------------------------------------------------------------------------------------+
// | Reserved | Extended Family ID | Extended Model ID | Reserved | Processor Type | Family ID | Model | Stepping ID |
// +-----------------------------------------------------------------------------------------------------------------+
#[derive(Clone, Copy, Debug)]
pub struct ProcessorVersion(u32);
impl ProcessorVersion {
    const STEPPING_OFFSET: u32 = 0;
    const MODEL_OFFSET: u32 = 4;
    const FAMILY_ID_OFFSET: u32 = 8;
    const PROCESSOR_TYPE_OFFSET: u32 = 12;
    const EXTENDED_MODEL_OFFSET: u32 = 16;
    const EXTENDED_FAMILY_ID_OFFSET: u32 = 20;

    const STEPPING_MASK: u32 = 0b1111 << Self::STEPPING_OFFSET;
    const MODEL_MASK: u32 = 0b1111 << Self::MODEL_OFFSET;
    const FAMILY_ID_MASK: u32 = 0b1111 << Self::FAMILY_ID_OFFSET;
    const PROCESSOR_TYPE_MASK: u32 = 0b11 << Self::PROCESSOR_TYPE_OFFSET;
    const EXTENDED_MODEL_MASK: u32 = 0b1111 << Self::EXTENDED_MODEL_OFFSET;
    const EXTENDED_FAMILY_ID_MASK: u32 = 0b1111_1111 << Self::EXTENDED_FAMILY_ID_OFFSET;

    // 4 bits
    pub fn stepping_id(&self) -> u8 {
        self.fetch(Self::STEPPING_MASK, Self::STEPPING_OFFSET)
    }

    // 4 bits
    pub fn model(&self) -> u8 {
        self.fetch(Self::MODEL_MASK, Self::MODEL_OFFSET)
    }

    // 4 bits
    pub fn family_id(&self) -> u8 {
        self.fetch(Self::FAMILY_ID_MASK, Self::FAMILY_ID_OFFSET)
    }

    pub fn processor_type(&self) -> ProcessorType {
        match self.fetch(Self::PROCESSOR_TYPE_MASK, Self::PROCESSOR_TYPE_OFFSET) {
            0b00 => ProcessorType::Oem,
            0b01 => ProcessorType::IntelOverdrive,
            0b10 => ProcessorType::DualProcessor,
            0b11 => ProcessorType::Reserved,
            b => unreachable!(
                "processor type is only 2 bits. mask_bits: {:b}. got value: {:b}",
                Self::PROCESSOR_TYPE_MASK,
                b
            ),
        }
    }

    // 4 bits
    pub fn extended_model(&self) -> u8 {
        self.fetch(Self::EXTENDED_MODEL_MASK, Self::EXTENDED_MODEL_OFFSET)
    }

    // 8 bits
    pub fn extended_family_id(&self) -> u8 {
        self.fetch(
            Self::EXTENDED_FAMILY_ID_MASK,
            Self::EXTENDED_FAMILY_ID_OFFSET,
        )
    }

    fn fetch(&self, mask: u32, offset: u32) -> u8 {
        ((self.0 & mask) >> offset) as u8
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ProcessorType {
    Oem,
    IntelOverdrive,
    DualProcessor,
    Reserved,
}

#[derive(Clone, Copy, Debug)]
pub struct ProcessorFeatures {
    ecx: u32,
    edx: u32,
}

macro_rules! gen_processor_feature {
    ($feature_name:ident, $field:ident, $offset:literal) => {
        impl ProcessorFeatures {
            pub fn $feature_name(&self) -> bool {
                (self.$field & (0b1 << $offset)) >> $offset == 0b1
            }
        }
    };
}

gen_processor_feature!(has_onboard_x87_fpu, edx, 0);
gen_processor_feature!(has_virt_8086_extensions, edx, 1);
gen_processor_feature!(has_debugging_extensions, edx, 2);
gen_processor_feature!(has_page_size_extension, edx, 3);
gen_processor_feature!(has_time_stamp_counter, edx, 4);
gen_processor_feature!(has_model_specific_registers, edx, 5);
gen_processor_feature!(has_phsyical_address_extension, edx, 6);
gen_processor_feature!(has_machine_check_extension, edx, 7);
gen_processor_feature!(has_64bit_compare_and_swap, edx, 8);
gen_processor_feature!(has_onboard_apic, edx, 9);
gen_processor_feature!(has_sysenter_sysexit, edx, 11);
gen_processor_feature!(has_memory_type_range_registers, edx, 12);
gen_processor_feature!(has_page_global_enable_bit_in_cr4, edx, 13);
gen_processor_feature!(has_machine_check_architecture, edx, 14);
gen_processor_feature!(has_conditional_move, edx, 15);
gen_processor_feature!(has_page_attribute_table, edx, 16);
gen_processor_feature!(has_36_bit_page_size_extension, edx, 17);
gen_processor_feature!(has_processor_serial_number, edx, 18);
gen_processor_feature!(has_cache_line_flush, edx, 19);
gen_processor_feature!(has_no_execute_bit, edx, 20);
gen_processor_feature!(has_debug_store, edx, 21);
gen_processor_feature!(has_onboard_thermal_control_msrs, edx, 22);
gen_processor_feature!(has_mmx, edx, 23);
gen_processor_feature!(has_fx_save_restore, edx, 24);
gen_processor_feature!(has_sse, edx, 25);
gen_processor_feature!(has_sse2, edx, 26);
gen_processor_feature!(has_cpu_cache_self_snooping, edx, 27);
gen_processor_feature!(has_max_apic_ids_reserved_field_is_valid, edx, 28);
gen_processor_feature!(has_automatic_thermal_monitor_temp_limiting, edx, 29);
gen_processor_feature!(has_ia64_emulating_x86, edx, 30);
gen_processor_feature!(has_pending_break_enable_wakeup_capability, edx, 31);

gen_processor_feature!(has_sse3, ecx, 0);
gen_processor_feature!(has_carryless_multiplication, ecx, 1);
gen_processor_feature!(has_64_bit_debug_store, ecx, 2);
gen_processor_feature!(has_monitor, ecx, 3);
gen_processor_feature!(has_cpl_qualified_debug_store, ecx, 4);
gen_processor_feature!(has_virutal_machine_extensions, ecx, 5);
gen_processor_feature!(has_safer_mode_extensions, ecx, 6);
gen_processor_feature!(has_enhanced_speedstep, ecx, 7);
gen_processor_feature!(has_thermal_monitor_2, ecx, 8);
gen_processor_feature!(has_supplemental_sse3, ecx, 9);
gen_processor_feature!(has_l1_context_id, ecx, 10);
gen_processor_feature!(has_silicon_debug_interface, ecx, 11);
gen_processor_feature!(has_fused_multiply_add, ecx, 12);
gen_processor_feature!(has_128bit_compare_and_swap, ecx, 13);
gen_processor_feature!(has_task_priority_message_disabling, ecx, 14);
gen_processor_feature!(has_perfmon_and_debug_capability, ecx, 15);
gen_processor_feature!(has_process_context_ids, ecx, 17);
gen_processor_feature!(has_direct_cache_access_for_dma_writes, ecx, 18);
gen_processor_feature!(has_sse_4_dot_1, ecx, 19);
gen_processor_feature!(has_sse_4_dot_2, ecx, 20);
gen_processor_feature!(has_x2apic, ecx, 21);
gen_processor_feature!(has_movbe, ecx, 22);
gen_processor_feature!(has_popcnt, ecx, 23);
gen_processor_feature!(has_apic_oneshot_via_tsc_deadline, ecx, 24);
gen_processor_feature!(has_aes, ecx, 25);
gen_processor_feature!(has_xsave, ecx, 26);
gen_processor_feature!(has_xsave_enabled_by_os, ecx, 27);
gen_processor_feature!(has_avx, ecx, 28);
gen_processor_feature!(has_fp_conversion_16bit, ecx, 29);
gen_processor_feature!(has_rdrand, ecx, 30);
gen_processor_feature!(has_hypervisor_present, ecx, 31);

#[derive(Clone, Copy, Debug)]
pub struct ProcessorInfo {
    version: ProcessorVersion,
    features: ProcessorFeatures,
    brand_index: u8,
    // CLFLUSH line size (Value * 8 = cache line size in bytes; used also by CLFLUSHOPT)
    clflush_line_size: u8,
    // Maximum number of addressable IDs for logical processors in this physical package*.
    max_addressible_logical_processor_ids: u8,
    lapic_id: u8,
}

impl ProcessorInfo {
    fn new(eax: u32, ebx: u32, ecx: u32, edx: u32) -> Self {
        let version = ProcessorVersion(eax);
        let features = ProcessorFeatures { ecx, edx };
        let brand_index = ebx as u8;
        let clflush_line_size = (ebx >> 8) as u8;
        let max_addressible_logical_processor_ids = (ebx >> 16) as u8;
        let lapic_id = (ebx >> 24) as u8;

        Self {
            version,
            features,
            brand_index,
            clflush_line_size,
            max_addressible_logical_processor_ids,
            lapic_id,
        }
    }

    pub fn version(&self) -> ProcessorVersion {
        self.version
    }

    pub fn features(&self) -> ProcessorFeatures {
        self.features
    }

    pub fn brand_index(&self) -> u8 {
        self.brand_index
    }

    pub fn clflush_line_size(&self) -> u8 {
        self.clflush_line_size
    }

    pub fn max_addressible_logical_processor_ids(&self) -> u8 {
        self.max_addressible_logical_processor_ids
    }

    pub fn lapic_id(&self) -> u8 {
        self.lapic_id
    }
}
