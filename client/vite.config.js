import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';
export default defineConfig({
    plugins: [react()],
    server: {
        host: '::1',
        port: 5000,
        strictPort: true,
        allowedHosts: ['shine.athergrid.dev'],
        proxy: {
            '/api': {
                target: 'http://[::1]:5001',
                changeOrigin: true,
            },
            '/auth': {
                target: 'http://[::1]:5001',
                changeOrigin: true,
            },
        },
    },
});
