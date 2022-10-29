/*
 * @licstart The following is the entire license notice for the
 * JavaScript code in this file.
 *
 * Decompression code adapted from UCL
 * Copyright (C) 1996-2002 Markus Franz Xaver Johannes Oberhumer
 *
 * jztool
 * Copyright (C) 2021 Aidan MacDonald
 *
 * jztool.js
 * Copyright (C) 2021 astrolabe
 * Copyright (C) 2022 Aidan MacDonald
 *
 * The JavaScript code in this file is free software: you can
 * redistribute it and/or modify it under the terms of the GNU
 * General Public License (GNU GPL) as published by the Free Software
 * Foundation, either version 2 of the License, or (at your option)
 * any later version.  The code is distributed WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU GPL for more details.
 *
 * @licend The above is the entire license notice for the JavaScript
 * code in this file.
 */

const VERSION = '1.0';

/* ============================================================================
 * UTILITIES
 * ========================================================================= */

function read_le32(buf, offset) {
    let ub = buf.buffer;
    if(ub.byteLength - offset < 4)
        throw new Error("buffer read out of bounds");

    return new DataView(ub).getUint32(offset, true);
}

function read_be32(buf, offset) {
    let ub = buf.buffer;
    if(ub.byteLength - offset < 4)
        throw new Error("buffer read out of bounds");

    return new DataView(ub).getUint32(offset, false);
}

function buf_eq(buf, offset, xbuf) {
    if(offset + xbuf.length > buf.length)
        return false;

    for(let ix = 0; ix < xbuf.length; ++ix)
        if(buf[offset + ix] !== xbuf[ix])
            return false;

    return true;
}

function buf_from_str(str) {
    let dat = [];
    for(let ix = 0; ix < str.length; ++ix)
        dat.push(str.charCodeAt(ix));

    return new Uint8Array(dat);
}

// https://stackoverflow.com/a/23451803
function buf_download(buf, name) {
    let blob = new Blob([buf], {type: "application/octet-stream"});
    let url = window.URL.createObjectURL(blob);

    let a = document.createElement("a");
    a.id = "buffer-download-link";
    a.style = "display: none";
    a.href = url;
    a.download = name;

    document.body.appendChild(a);
    a.click();
    window.URL.revokeObjectURL(url);
    document.body.removeChild(a);
}

/* ============================================================================
 * UCL DECOMPRESSOR & UNPACKER
 * ========================================================================= */

function ucl_nrv2e_decompress(src) {
    let bit = 0;
    let ilen = 0;
    let last_m_off = 1;
    let dst = [];

    const E_INPUT_OVERRUN = "UCL: input overrun";
    const E_LOOKBEHIND_OVERRUN = "UCL: lookbehind overrun";

    function fail(cond, err) {
        if(cond)
            throw new Error(err);
    }

    function get_bit() {
        bit = bit & 0x7f ? (bit << 1) : (src[ilen++] << 1) + 1;
        return (bit >> 8) & 1;
    }

    while(true) {
        let m_off, m_len;

        while(get_bit()) {
            fail(ilen >= src.length, E_INPUT_OVERRUN);
            dst.push(src[ilen++]);
        }

        m_off = 1;
        while(true) {
            m_off = m_off*2 + get_bit();
            fail(ilen >= src.length, E_INPUT_OVERRUN);
            fail(m_off > 0xffffff + 3, E_LOOKBEHIND_OVERRUN);
            if(get_bit())
                break;
            m_off = (m_off - 1)*2 + get_bit();
        }

        if(m_off === 2) {
            m_off = last_m_off;
            m_len = get_bit();
        } else {
            fail(ilen >= src.length, E_INPUT_OVERRUN);
            m_off = (m_off - 3)*256 + src[ilen++];
            if(m_off === 0xffffffff)
                break;

            m_len = (m_off ^ 0xffffffff) & 1;
            m_off >>= 1;
            last_m_off = ++m_off;
        }

        if(m_len > 0)
            m_len = 1 + get_bit();
        else if(get_bit())
            m_len = 3 + get_bit();
        else {
            m_len++;
            do {
                m_len = m_len*2 + get_bit();
                fail(ilen >= src.length, E_INPUT_OVERRUN);
            } while(!get_bit());
            m_len += 3;
        }

        if(m_off > 0x500)
            m_len++;

        fail(m_off > dst.length, E_LOOKBEHIND_OVERRUN);

        let lb_off = dst.length - m_off;
        dst.push(dst[lb_off++]);

        for(let ix = 0; ix < m_len; ++ix)
            dst.push(dst[lb_off++]);
    }

    return dst;
}

function ucl_unpack(src){
    if(src.length < 18)
        throw new Error('UCL: input is too short for header');

    const magic = [0x00, 0xe9, 0x55, 0x43, 0x4c, 0xff, 0x01, 0x1a];
    const method = src[12];
    const block_size = read_be32(src, 14);

    if(!buf_eq(src, 0, magic))
        throw new Error('UCL: invalid magic');
    if(method !== 0x2e)
        throw new Error('UCL: unsupported method');
    if(block_size < 1024 || block_size > 8*1024*1024)
        throw new Error('UCL: invalid block size');

    let pos = 18;
    let dst = [];
    while(true) {
        const out_len = read_be32(src, pos);
        pos += 4;
        if(out_len === 0)
            break;
        if(src.length - pos < 4)
            throw new Error('UCL: unexpected EOF');

        const in_len = read_be32(src, pos);
        pos += 4;
        if(in_len > block_size || out_len > block_size || in_len === 0 || in_len > out_len)
            throw new Error('UCL: invalid lengths');
        if(src.length - pos < in_len)
            throw new Error('UCL: unexpected EOF');

        if(in_len < out_len) {
            const out = ucl_nrv2e_decompress(src.slice(pos, pos + in_len));
            if(out.length !== out_len)
                throw new Error('UCL: decompressed the incorrect amount');

            dst = dst.concat(out);
        } else {
            for(let ix = 0; ix < in_len; ix++)
                dst.push(src[pos + ix]);
        }

        pos += in_len;
    }

    return Uint8Array.from(dst);
}

/* ============================================================================
 * TAR FILE EXTRACTION
 * ========================================================================= */

function tar_extract(tar, filename, optional) {
    const BLOCK_SIZE = 512;

    const NAME_OFF   = 0;   const NAME_LEN   = 100;
    const SIZE_OFF   = 124; const SIZE_LEN   = 12;
    const CHKSUM_OFF = 148; const CHKSUM_LEN = 8;
    const TYPE_OFF   = 156;

    const T_REG = 0x30; // regular file

    function read_str(buf, offset, max_length) {
        if(buf.length - offset < max_length)
            throw new Error("Tar: unexpected EOF");

        let s = "";
        for(let ix = 0; ix < max_length; ++ix) {
            const ch = buf[offset + ix];
            if(ch === 0)
                break;

            s += String.fromCharCode(ch);
        }

        return s;
    }

    function read_octal(buf, offset, max_length) {
        let n = 0;
        for(let ix = 0; ix < max_length; ix++) {
            const c = buf[offset + ix];
            if(c === 0)
                break;
            if(c < 0x30 || c > 0x37)
                throw new Error('Tar: invalid octal digit');

            n *= 8;
            n += c - 0x30;
        }

        return n;
    }

    function calc_checksum(buf, offset) {
        if(buf.length - offset < BLOCK_SIZE)
            throw new Error('Tar: unexpected EOF');

        const u32_max = 0xffffffff;
        let res = 256;

        for(let ix = 0; ix < CHKSUM_OFF; ++ix)
            res = (res + buf[offset + ix]) & u32_max;
        for(let ix = CHKSUM_OFF+CHKSUM_LEN; ix < BLOCK_SIZE; ++ix)
            res = (res + buf[offset + ix]) & u32_max;
        return res;
    }

    function read_header(buf, offset) {
        if(buf.length - offset < BLOCK_SIZE)
            throw new Error('Tar: unexpected EOF');

        // Assume end of archive if there is no checksum
        if(buf[offset + CHKSUM_OFF] === 0)
            return null;

        const checksum = read_octal(buf, offset + CHKSUM_OFF, CHKSUM_LEN);
        if(checksum !== calc_checksum(buf, offset))
            throw new Error('Tar: checksum mismatch at offset ' + offset);

        return {
            name: read_str(buf, offset + NAME_OFF, NAME_LEN),
            size: read_octal(buf, offset + SIZE_OFF, SIZE_LEN),
            type: buf[offset+TYPE_OFF] ? buf[offset+TYPE_OFF] : T_REG,
        };
    }

    let offset = 0;
    while(true) {
        const header = read_header(tar, offset);
        offset += BLOCK_SIZE;
        if(header === null)
            break;

        if(header.name === filename) {
            if(header.type !== T_REG)
                throw new Error('Tar: ' + filename + ' is not a regular file');

            return tar.slice(offset, offset + header.size);
        }

        offset += header.size;
        if((header.size % BLOCK_SIZE) !== 0)
            offset += BLOCK_SIZE - (header.size % BLOCK_SIZE);
    }

    if(optional === true)
        return null;

    throw new Error('Tar: file \'' + filename + '\' not found in archive');
}

/* ============================================================================
 * PACKAGE AND IMAGE UTILITIES
 * ========================================================================= */

function get_pkg_version(meta_txt) {
    const index = meta_txt.indexOf('\n');
    if(index < 0)
        throw new Error("Package: Version metadata is malformed");

    return meta_txt.slice(0, index);
}

function search_bin_header(buf, label) {
    if(label.length !== 4)
        throw new Error("Binary header label must be 4 bytes long");

    const HDR_BEGIN = 128; // Header begins within this many bytes
    const HDR_LEN   = 256; // Maxmimum length of header, in bytes

    const magic_BEGINHDR = buf_from_str("BEGINHDR");
    const magic_ENDH     = buf_from_str("ENDH");
    const magic_label    = buf_from_str(label);

    // Calculate search bound
    let search_len = Math.min(buf.length, HDR_LEN);
    if(search_len < 8)
        return null;
    search_len -= 7;

    // Locate the beginning of the header
    let ix = 8;
    for(; ix < search_len; ix += 4)
        if(buf_eq(buf, ix, magic_BEGINHDR))
            break;
    if(ix >= search_len)
        return null;

    // Search for the label within the header
    search_len = Math.min(buf.length, ix + HDR_LEN) - 7;
    for(; ix < search_len; ix += 8) {
        if(buf_eq(buf, ix, magic_ENDH))
            break;

        if(buf_eq(buf, ix, magic_label))
            return read_le32(buf, ix + 4);
    }

    return null;
}

/* ============================================================================
 * INGENIC USB BOOT PROTOCOL
 * ========================================================================= */

const CPU_X1000 = "x1000";

const CPU_INFO = {
    "x1000": {
        vendor_id: 0xa108,
        product_id: 0x1000,
    },
};

const VR_SET_DATA_ADDRESS = 1;
const VR_SET_DATA_LENGTH = 2;
const VR_FLUSH_CACHES = 3;
const VR_PROGRAM_START1 = 4;
const VR_PROGRAM_START2 = 5;

async function usb_vendor_req(device, request, argument) {
    await device.controlTransferOut({
        requestType: 'vendor',
        recipient: 'device',
        request: request,
        value: argument >> 16,
        index: argument & 0xffff
    }, new Uint8Array(0));
}

async function usb_send(device, address, data) {
    await usb_vendor_req(device, VR_SET_DATA_ADDRESS, address);
    await usb_vendor_req(device, VR_SET_DATA_LENGTH, data.length);
    await device.transferOut(1, data);
}

const X1000_TCSM_BASE = 0xf4000000;

const X1000_SPL_LOAD_ADDR = X1000_TCSM_BASE + 0x1000;
const X1000_SPL_EXEC_ADDR = X1000_TCSM_BASE + 0x1800;

const X1000_STANDARD_DRAM_BASE = 0x80004000;

async function x1000_run_stage1(device, image) {
    await usb_send(device, X1000_SPL_LOAD_ADDR, image);
    await usb_vendor_req(device, VR_PROGRAM_START1, X1000_SPL_EXEC_ADDR);
}

async function x1000_run_stage2(device, image) {
    let load_addr = search_bin_header(image, "LOAD");
    if(load_addr === null)
        load_addr = X1000_STANDARD_DRAM_BASE;

    await usb_send(device, load_addr, image);
    await usb_vendor_req(device, VR_FLUSH_CACHES, 0);
    await usb_vendor_req(device, VR_PROGRAM_START2, load_addr);
}

/* ============================================================================
 * FRONTEND
 * ========================================================================= */

const BASEURL = "files";

const PLAYER_INFO = {
    "m3k": {
        name: "FiiO M3K",
        file_ext: "m3k",
        bootloader_url: BASEURL + "/bootloader/fiio/m3k/221029-b4e7c60c6d/bootloader.m3k",
        boot_button: "Volume Down",
        cpu: CPU_X1000,
    },
    "q1": {
        name: "Shanling Q1",
        file_ext: "q1",
        bootloader_url: BASEURL + "/bootloader/shanling/q1/221029-b4e7c60c6d/bootloader.q1",
        boot_button: "Play",
        cpu: CPU_X1000,
    },
    "erosq": {
        name: "AIGO Eros Q",
        file_ext: "erosq",
        bootloader_url: BASEURL + "/bootloader/aigo/native/221029-b4e7c60c6d/bootloader.erosq",
        boot_button: "Menu",
        cpu: CPU_X1000,
    },
};

window.addEventListener('DOMContentLoaded', function(){
    const debug_console = document.getElementById('console');
    let download_cache = {};
    let package_cache = {};

    function debug_log(item) {
        debug_console.value += item + '\n';
    }

    async function retrieve_file(file_name, url) {
        debug_log("Downloading: '" + url + "'");

        let resp = await fetch(url);
        if(!resp.ok)
            throw new Error("Error downloading file: " + resp.statusText + " (" + resp.status + ")");

        let ret = new Uint8Array(await resp.arrayBuffer());
        debug_log("File downloaded, " + ret.byteLength + " bytes");

        return ret;
    }

    async function retrieve_file_cached(file_name, url) {
        let file = download_cache[file_name];
        if(file === undefined) {
            file = await retrieve_file(file_name, url);
            download_cache[file_name] = file;
        }

        return file;
    }

    function get_player_model() {
        let elem = document.getElementById('select-player-model');
        return elem.value;
    }

    function get_player_info() {
        let model = get_player_model();
        return PLAYER_INFO[model];
    }

    function get_cpu_info() {
        let player_info = get_player_info();
        if(player_info === undefined)
            return undefined;

        return CPU_INFO[player_info.cpu];
    }

    function load_package(pkg) {
        const player_model = get_player_model();
        const player_info = get_player_info();
        if(player_info === undefined)
            return null;

        debug_log("Extracting bootloader-info.txt...");
        let meta_file = tar_extract(pkg, 'bootloader-info.txt');
        let meta_text = new TextDecoder().decode(meta_file);

        let spl_filename = 'spl.' + player_info.file_ext;
        debug_log("Extracting " + spl_filename + "...")
        let spl_img = tar_extract(pkg, spl_filename);

        debug_log("Extracting bootloader image...");
        let boot_ucl = tar_extract(pkg, 'bootloader2.ucl', true);
        if(boot_ucl !== null) {
            debug_log("Found bootloader2.ucl (v2 format)");
        } else {
            boot_ucl = tar_extract(pkg, 'bootloader.ucl');
            debug_log("Found bootloader.ucl (v1 format)");
        }

        let boot_img = ucl_unpack(boot_ucl);

        ret = {
            version: get_pkg_version(meta_text),
            spl_img: spl_img,
            boot_img: boot_img,
        };

        debug_log("Validated bootloader package.");
        debug_log("Bootloader version: " + ret.version);

        package_cache[player_model] = ret;
        return ret;
    }

    function update_ui_state() {
        const model = get_player_model();
        const info = get_player_info();
        const pkg = package_cache[model];

        // Update the boot button text
        Array.from(document.getElementsByClassName('boot-button'))
            .forEach(function(x) {
                if(info !== undefined)
                    x.innerText = info.boot_button;
                else
                    x.innerText = "USB boot";
            });

        // Update the version placeholder text
        Array.from(document.getElementsByClassName('bootloader-version'))
            .forEach(function(x) {
                if(pkg !== undefined)
                    x.innerText = pkg.version;
                else
                    x.innerText = "unknown";
            });

        // Enable/disable actions based on bootloader package presence
        Array.from(document.getElementsByClassName('enable-if-boot-pkg'))
            .forEach(x => x.disabled = (pkg === undefined));
        Array.from(document.getElementsByClassName('disable-if-boot-pkg'))
            .forEach(x => x.disabled = (pkg !== undefined));
        Array.from(document.getElementsByClassName('show-if-boot-pkg'))
            .forEach(x => x.hidden = (pkg === undefined));
        Array.from(document.getElementsByClassName('hide-if-boot-pkg'))
            .forEach(x => x.hidden = (pkg !== undefined));

        // Disable elements if player selection is invalid
        if(info === undefined) {
            Array.from(document.getElementsByClassName('disable-if-no-player'))
                .forEach(x => x.disabled = true);
        }

        // Show/hide elements based on WebUSB support
        Array.from(document.getElementsByClassName('show-if-webusb'))
            .forEach(x => x.hidden = (navigator.usb === undefined));
        Array.from(document.getElementsByClassName('hide-if-webusb'))
            .forEach(x => x.hidden = (navigator.usb !== undefined));
    }

    function add_button(id, callback){
        const el = document.getElementById(id);

        el.addEventListener('click', function(){
            el.disabled = true;
            callback().catch(function(e){
                debug_log(e);
            });

            el.disabled = false;
        });
    }

    document.getElementById('select-player-model')
        .addEventListener('change', function() {
            update_ui_state();
        });

    add_button('clear-log', async function() {
        debug_console.value = "";
    });

    add_button('button-download', async function() {
        const info = get_player_info();
        if(info !== undefined) {
            let pkg = await retrieve_file_cached('bootloader.' + info.file_ext,
                                                 info.bootloader_url);
            load_package(pkg);
            update_ui_state();
        }
    });

    add_button('button-save', async function() {
        const info = get_player_info();
        if(info === undefined)
            throw new Error('No player info');

        const file_name = 'bootloader.' + info.file_ext
        const file = download_cache[file_name];
        const pkg = package_cache[get_player_model()]
        if(file === undefined || pkg === undefined)
            throw new Error('Package is missing or invalid');

        debug_log("Saving bootloader...");
        buf_download(file, file_name);
    });

    add_button('button-load', async function() {
        if(navigator.usb === undefined)
            throw new Error('This browser does not support WebUSB');

        const player_info = get_player_info();
        if(player_info === undefined)
            throw new Error('Invalid player selection');

        const cpu_info = get_cpu_info();
        if(cpu_info === undefined)
            throw new Error('Invalid CPU for player: ' + player_info.cpu);

        const boot_pkg = package_cache[get_player_model()]
        if(boot_pkg === undefined)
            throw new Error('Missing bootloader package');

        debug_log('Asking for device...');
        let device = await navigator.usb.requestDevice({
            filters: [{
                vendorId: cpu_info.vendor_id,
                productId: cpu_info.product_id,
            }]
        });

        debug_log('Opening device...');
        await device.open();

        try {
            debug_log('Claiming device interface...');
            await device.claimInterface(0);

            debug_log('Loading stage1 (SPL)...');
            await x1000_run_stage1(device, boot_pkg.spl_img);

            debug_log('Pausing for SPL to come up...');
            await new Promise(x => setTimeout(x, 500));

            debug_log('Loading stage2 (bootloader)...');
            await x1000_run_stage2(device, boot_pkg.boot_img);

            debug_log('Closing device...');
            await device.close();

            debug_log('Done!');
        } catch(e) {
            await device.close();
            throw e;
        }
    });

    update_ui_state();
});
